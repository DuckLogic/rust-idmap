#![cfg(features = "compact")]
//! A more compact `IdMap`, where indexes are offset from the start element.

// TODO: Reduce code duplication with `IdMap`

/// A map of mostly-contiguous `IntegerId` keys to values, backed by a `VecDeque`
/// This is more compact than the `IdMap` since the indexes are offset from the start element.
/// For example, a map with keys `[1000, 1001, 1003]` is perfectly efficient,
/// since it only allocates storage for 4 nodes, instead of 1000 like `IdMap` would.
/// Insertions are still always O(1), since a `VecDeque` allows the offset to be reduced.
/// Insertion order is maintained, as there's an indirection into an entry array like in `OrderMap`.
/// Therefore, entries which aren't present take less space, as they only need to store the index.
#[derive(Clone)]
pub struct CompactIdMap<K: IntegerId, V> {
    offset: usize,
    table: VecDeque<u32>,
    entries: Vec<(K, V)>,
}
impl<K: IntegerId, V> CompactIdMap<K, V> {
    #[inline]
    pub fn new() -> Self {
        Self::with_capacity(0)
    }
    pub fn with_capacity(capacity: usize) -> Self {
        CompactIdMap {
            offset: 0,
            table: VecDeque::with_capacity(capacity),
            entries: Vec::with_capacity(capacity)
        }
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() > 0
    }
    #[inline]
    pub fn len(&self) -> usize {
        self.entries.len()
    }
    #[inline]
    pub fn get(&self, key: &K) -> Option<&V> {
        let id = key.id();
        if let Some(entry_index) = self.entry_index(id) {
            // NOTE: !0 is used to mark missing entries
            if let Some(&(ref actual_key, ref value)) = self.entries.get(entry_index as usize) {
                debug_assert_eq!(*actual_key, *key, "Duplicate keys with id {}", key.id());
                return Some(value)
            }
        }
        None
    }
    #[inline]
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let id = key.id();
        if let Some(entry_index) = self.entry_index(id) {
            // NOTE: !0 is used to mark missing entries
            if let Some(&mut (ref actual_key, ref mut value)) = self.entries.get_mut(entry_index as usize) {
                debug_assert_eq!(actual_key, key, "Duplicate keys with id {}", key.id());
                return Some(value)
            }
        }
        None
    }
    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let id = usize::try_from(key.id()).expect("ID overflowed isize!");
        assert_ne!(id, !0, "Invalid id: {}", id);
        if let Some(index) = id.checked_sub(self.offset) {
            if let Some(&entry_index) = self.table.get(index) {
                if entry_index != !0 {
                    return Some(mem::replace(&mut self.entries[entry_index as usize], (key, value)).1)
                }
            }
            // No existing entry, but we don't need to change the offset
            while self.table.len() <= index {
                self.table.push_back(!0)
            }
            debug_assert_eq!(self.table[index], !0);
            let entry_index = u32::try_from(self.entries.len()).expect("Length overflowed u32");
            self.entries.push((key, value));
            self.table[index] = entry_index;
            None
        } else {
            // We need to decrease the offset
            debug_assert!(self.offset > id);
            let offset_decrease = self.offset - id;
            for _ in 0..offset_decrease {
                self.table.push_front(!0);
            }
            self.offset -= offset_decrease;
            debug_assert_eq!(id, self.offset);
            let entry_index = u32::try_from(self.entries.len()).expect("Length overflowed u32");
            self.entries.push((key, value));
            self.table[0] = entry_index;
            None
        }
    }
    pub fn remove(&mut self, key: &K) -> Option<V> {
        if let Some(entry_index) = self.entry_index(key.id()) {
            if entry_index != !0 {
                return Some(self.remove_at(entry_index))
            }
        }
        None
    }
    fn remove_at(&mut self, entry_index: u32) -> V {
        let id = self.entries[entry_index as usize].0.id();
        let table_index = (id - self.offset as u64) as usize;
        let actual_entry_index = mem::replace(&mut self.table[table_index], !0);
        assert_eq!(actual_entry_index, entry_index);
        debug_assert!(!self.entries.is_empty());
        let last_entry_index = (self.entries.len() - 1) as u32;
        let (_, value) = self.entries.swap_remove(entry_index as usize);
        if entry_index != last_entry_index {
            self.update_moved_entry(last_entry_index, entry_index);
        }
        value
    }
    fn update_moved_entry(&mut self, old_index: u32, new_index: u32) {
        assert!(old_index != !0 || new_index != !0, "Invalid indexes: {}, {}", old_index, new_index);
        // NOTE: Check the new index, as this must be performed _after_ the entry has moved
        let &(ref key, _) = &self.entries[new_index as usize];
        let table_index = self.entry_index(key.id()).unwrap() as usize;
        let old_value = mem::replace(&mut self.table[table_index], new_index);
        assert_eq!(old_value, old_index);
    }
    pub fn shrink_to_fit(&mut self) {
        if !self.table.is_empty() {
            let mut start_element = 0;
            for (index, &entry_index) in self.table.iter().enumerate() {
                if entry_index != !0 {
                    start_element = index;
                    break
                }
            }
            let mut end_element = self.table.len() - 1;
            for (index, &entry_index) in self.table.iter().enumerate().rev() {
                if entry_index != !0 {
                    end_element = index + 1;
                    break
                }
            }
            self.table.drain(..start_element);
            self.table.drain(end_element..);
        }
        self.table.shrink_to_fit();
        self.entries.shrink_to_fit();
    }
    #[inline]
    pub fn entry<Q: ToOwned>(&mut self, key: &K) -> Entry<K, V> {
        if let Some(entry_index) = self.entry_index(key.id()) {
            if entry_index != !0 {
                return Entry::Occupied(OccupiedEntry {
                    map: self, entry_index
                })
            }
        }
        Entry::Vacant(VacantEntry {
            map: self, key
        })
    }
    #[inline]
    pub fn iter(&self) -> Iter<K, V> {
        Iter(self.entries.iter())
    }
    #[inline]
    fn entry_index(&self, id: u64) -> Option<u32> {
        if let Ok(id) = usize::try_from(id) {
            if let Some(index) = id.checked_sub(self.offset) {
                if let Some(&entry_index) = self.table.get(index) {
                    return Some(entry_index)
                }
            }
        }
        None
    }
}
impl<K: IntegerId, V> Default for CompactIdMap<K, V> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}
pub enum Entry<'a, K: IntegerId + 'a, V: 'a> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>)
}
impl<'a, K: IntegerId, V> Entry<'a, K, V> {
    #[inline]
    pub fn or_insert(self, value: V) -> &'a mut V {
        self.or_insert_with(|| value)
    }
    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, func: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => {
                &mut entry.map.entries[entry.entry_index as usize].1
            },
            Entry::Vacant(entry) => {
                let id = entry.key.id();
                assert!(entry.map.insert(entry.key, func()).is_none());
                let entry_index = entry.map.entry_index(id).unwrap();
                &mut entry.map.entries[entry_index as usize].1
            }
        }
    }
}
pub struct OccupiedEntry<'a, K: IntegerId + 'a, V: 'a> {
    map: &'a mut CompactIdMap<K, V>,
    entry_index: u32
}
pub struct VacantEntry<'a, K: IntegerId + 'a, V: 'a> {
    map: &'a mut CompactIdMap<K, V>,
    key: K
}
impl<'a, K: IntegerId + 'a, V: 'a> OccupiedEntry<'a, K, V> {
     pub fn remove(self) -> V {
         self.map.remove_at(self.entry_index)
     }
}
impl<K: Debug + IntegerId, V: Debug> Debug for CompactIdMap<K, V> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut map = f.debug_map();
        for (key, value) in self.iter() {
            map.entry(key, value);
        }
        map.finish()
    }
}
