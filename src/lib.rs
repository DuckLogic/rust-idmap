//! Efficient maps of integer id keys to values, backed by an underlying `Vec`.
//! However, unless a `CompactIdMap` is used, space requirements are O(n) the largest key.
//! Any type that implements `IntegerId` can be used for the key,
//! but no storage is wasted if the key can be represented from the id.
#![feature(try_from, nonzero)]
extern crate core;
extern crate itertools;
#[cfg(feature="serde")]
extern crate serde;

use std::iter::{FromIterator, DoubleEndedIterator};
use std::{mem, slice, vec};
use std::borrow::Borrow;
use std::ops::{Index, IndexMut};
use std::fmt::{self, Debug, Formatter};

pub mod compact;
#[cfg(feature="serde")]
mod serialization;
mod utils;
mod integer_id;

pub use integer_id::IntegerId;

use itertools::Itertools;
use itertools::EitherOrBoth::*;
use utils::fill_bytes;

/// A map of mostly-contiguous `IntegerId` keys to values, backed by a `Vec`.
/// Unlike `CompactIdMap`, indexes are _not_ offset from the start element,
/// so a map with keys `[1000, 10001, 1003]` would allocate 1004 nodes!
/// However, insertions are always O(1) and it is noticeably faster than a `CompactIdMap`,
/// so should be used if the keys are known to start from zero.
/// Insertion order is maintained, as there's an indirection into an entry array like in `OrderMap`.
/// Therefore, entries which aren't present take less space, as they only need to store the index.
#[derive(Clone)]
pub struct IdMap<K: IntegerId, V> {
    table: Vec<u32>,
    entries: Vec<(K, V)>
}
impl<K: IntegerId, V> IdMap<K, V> {
    #[inline]
    pub fn new() -> Self {
        Self::with_capacity(0)
    }
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        IdMap {
            table: Vec::with_capacity(capacity),
            entries: Vec::with_capacity(capacity)
        }
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
    #[inline]
    pub fn len(&self) -> usize {
        self.entries.len()
    }
    pub fn max_id(&self) -> Option<usize> {
        if self.table.is_empty() {
            return None
        }
        let mut index = self.table.len() - 1;
        loop {
            let value = self.table[index];
            if value != !0 {
                return Some(value as usize);
            }
            if index > 0 {
                index -= 1;
            } else {
                return None;
            }
        }
    }
    #[inline]
    pub fn get<Q: Borrow<K>>(&self, key: Q) -> Option<&V> {
        let key = key.borrow();
        let id = key.id();
        if let Some(&entry_index) = self.table.get(id as usize) {
            // NOTE: !0 is used to mark missing entries, so handle out of bounds
            if let Some(&(ref actual_key, ref value)) = self.entries.get(entry_index as usize) {
                debug_assert_eq!(actual_key, key, "Duplicate keys with id {}", id);
                return Some(value);
            } else {
                debug_assert_eq!(entry_index, !0);
            }
        }
        None
    }
    #[inline]
    pub fn get_mut<Q: Borrow<K>>(&mut self, key: Q) -> Option<&mut V> {
        let key = key.borrow();
        let id = key.id();
        if let Some(&entry_index) = self.table.get(id as usize) {
            // NOTE: !0 is used to mark missing entries, so handle out of bounds
            if let Some(&mut (ref actual_key, ref mut value)) = self.entries.get_mut(entry_index as usize) {
                debug_assert_eq!(actual_key, key, "Duplicate keys with id {}", id);
                return Some(value);
            } else {
                debug_assert_eq!(entry_index, !0);
            }
        }
        None
    }
    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let id = key.id32();
        let entry_index = Self::mut_entry_index(&mut self.table, id);
        if let Some(&mut (ref actual_key, ref mut old_value)) = self.entries.get_mut(*entry_index as usize) {
            debug_assert_eq!(*actual_key, key, "Duplicate keys with id {}", id);
            return Some(mem::replace(old_value, value))
        }
        let new_entry = self.entries.len() as u32;
        self.entries.push((key, value));
        *entry_index = new_entry;
        None
    }
    #[inline]
    pub fn remove<Q: Borrow<K>>(&mut self, key: Q) -> Option<V> {
        let key = key.borrow();
        if let Some(&entry_index) = self.table.get(key.id() as usize) {
            if entry_index != !0 {
                return Some(self.remove_at(entry_index))
            }
        }
        None
    }
    fn remove_at(&mut self, entry_index: u32) -> V {
        let id = self.entries[entry_index as usize].0.id();
        let actual_entry_index = mem::replace(&mut self.table[id as usize], !0);
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
        let old_value = mem::replace(&mut self.table[key.id() as usize], new_index);
        assert_eq!(old_value, old_index);
    }
    #[inline]
    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        let id = key.id32();
        if let Some(&entry_index) = self.table.get(id as usize) {
            if entry_index != !0 {
                return Entry::Occupied(OccupiedEntry {
                    map: self,
                    entry_index
                })
            }
        }
        Entry::Vacant(VacantEntry { id, key, map: self })
    }
    #[inline]
    fn mut_entry_index(table: &mut Vec<u32>, index: u32) -> &mut u32 {
        // NOTE: We must look before we leap to work around the borrow checker
        if (index as usize) < table.len() {
            &mut table[index as usize]
        } else {
            Self::grow_entry_index(table, index)
        }
    }
    #[cold]
    fn grow_entry_index(table: &mut Vec<u32>, index: u32) -> &mut u32 {
        /*
         * Since the vector doubles the allocation each time we grow anyways,
         * we also fill the vector all the way up to its capacity.
         * This avoids growing very often, and amortizes the growth just like the Vec.
         */
        let len = table.len();
        if (index as usize) >= len {
            table.reserve((index as usize) - len + 1);
        }
        let additional_elements = table.capacity() - len;
        fill_bytes(table, additional_elements, !0);
        &mut table[index as usize]
    }
    #[inline]
    pub fn iter(&self) -> Iter<K, V> {
        Iter(self.entries.iter())
    }
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut(self.entries.iter_mut())
    }
    #[inline]
    pub fn keys(&self) -> Keys<K, V> {
        Keys(self.entries.iter())
    }
    #[inline]
    pub fn values(&self) -> Values<K, V> {
        Values(self.entries.iter())
    }
    #[inline]
    pub fn clear(&mut self) {
        self.entries.clear();
        self.table.clear();
    }
    /// Sort the map's entries by the specified function
    #[inline]
    pub fn sort_by<F, B: Ord>(&mut self, mut func: F) where F: FnMut(&K, &V) -> B {
        self.entries.sort_unstable_by_key(|&(ref key, ref value)| func(key, value))
    }
    /// Return a slice of the map's entries
    #[inline]
    pub fn entries(&self) -> &[(K, V)] {
        &self.entries
    }
    /// Retains only the elements specified by the predicate.
    /// ```
    /// # use idmap::VecMap;
    /// let mut map: IdMap<usize> = (0..8).map(|x|(x, x*10)).collect();
    /// map.retain(|k, _| k % 2 == 0);
    /// assert_eq!(map.into_iter().collect(), vec![(0, 0), (2, 20), (4, 40), (6, 60)]);
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut func: F) where F: FnMut(&K, &V) -> bool {
        let mut changed = false;
        self.entries.retain(|&(ref key, ref value)| {
            if func(key, value) {
                changed = true;
                true
            } else {
                false
            }
        });
        if !changed {
            self.correct_entries()
        }
    }
    fn correct_entries(&mut self) {
        self.table.clear();
        let table = &mut self.table;
        for (index, &(ref key, _)) in self.entries.iter().enumerate() {
            let id = key.id32();
            *Self::mut_entry_index(table, id) = index as u32;
        }
    }
}
/// Checks if two have the same contents, ignoring the order.
impl<K: IntegerId, V: PartialEq> PartialEq for IdMap<K, V> {
    fn eq(&self, other: &IdMap<K, V>) -> bool {
        // Since we can't rely on the ordering, we have to check the lookup tables first to find each map's entry. 
        if self.entries.len() != other.entries.len() {
            return false;
        }
        for zip in self.table.iter().zip_longest(other.table.iter()) {
            match zip {
                Both(&self_entry_index, &other_entry_index) => {
                    if self_entry_index == !0 || other_entry_index == !0 {
                        if other_entry_index != self_entry_index {
                            return false;
                        }
                    } else if self.entries[self_entry_index as usize].1 != other.entries[other_entry_index as usize].1 {
                        return false
                    }
                },
                Left(&entry_index) | Right(&entry_index) => {
                    if entry_index != !0 {
                        return false;
                    }
                }
            }
        }
        true
    }
}
/// Creates an `IDMap` from a list of key-value pairs
/// 
/// ## Example
/// ````
/// #[macro_use] extern crate idmap;
/// # fn main() {
/// let map = idmap! {
///     1 => "a",
///     25 => "b"
/// };
/// assert_eq!(map[1], "a");
/// assert_eq!(map[25], "b");
/// assert_eq!(map.get(26), None);
/// // 1 is the first key
/// assert_eq!(map.keys().next(), Some(&1));
/// # }
/// ````
#[macro_export]
macro_rules! idmap {
    ($($key:expr => $value:expr),*) => {
        {
            let entries = vec![$(($key, $value)),*];
            let mut result = $crate::IdMap::with_capacity(entries.len());
            result.extend(entries);
            result
        }
    };
}
impl<K: IntegerId, V> Default for IdMap<K, V> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}
impl<K: IntegerId, V> Index<K> for IdMap<K, V> {
    type Output = V;
    #[inline]
    fn index(&self, key: K) -> &V {
        &self[&key]
    }
}
impl<K: IntegerId, V> IndexMut<K> for IdMap<K, V> {
    #[inline]
    fn index_mut(&mut self, key: K) -> &mut V {
        &mut self[&key]
    }
}
impl<'a, K: IntegerId, V> Index<&'a K> for IdMap<K, V> {
    type Output = V;
    #[inline]
    fn index(&self, key: &'a K) -> &V {
        if let Some(value) = self.get(key) {
            value
        } else {
            panic!("Missing entry for {:?}", key)
        }
    }
}
impl<'a, K: IntegerId, V> IndexMut<&'a K> for IdMap<K, V> {
    #[inline]
    fn index_mut(&mut self, key: &'a K) -> &mut V {
        if let Some(value) = self.get_mut(key) {
            value
        } else {
            panic!("Missing entry for {:?}", key)
        }
    }
}
impl<K: IntegerId, V: Debug> Debug for IdMap<K, V> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut d = f.debug_map();
        for (key, value) in self.iter() {
            d.entry(key, value);
        }
        d.finish()
    }
}
pub enum Entry<'a, K: IntegerId + 'a, V: 'a> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>)
}
impl<'a, K: IntegerId + 'a, V: 'a> Entry<'a, K, V> {
    #[inline]
    pub fn or_insert(self, value: V) -> &'a mut V {
        self.or_insert_with(|| value)
    }
    #[inline]
    pub fn or_insert_with<F>(self, func: F) -> &'a mut V where F: FnOnce() -> V {
        match self {
            Entry::Occupied(entry) => entry.value(),
            Entry::Vacant(entry) => entry.or_insert_with(func)
        }
    }
}
pub struct OccupiedEntry<'a, K: IntegerId + 'a, V: 'a> {
    map: &'a mut IdMap<K, V>,
    entry_index: u32
}
impl<'a, K: IntegerId + 'a, V: 'a> OccupiedEntry<'a, K, V> {
    #[inline]
    pub fn value(self) -> &'a mut V {
        &mut self.map.entries[self.entry_index as usize].1
    }
}
pub struct VacantEntry<'a, K: IntegerId + 'a, V: 'a> {
    map: &'a mut IdMap<K, V>,
    key: K,
    id: u32
}
impl<'a, K: IntegerId + 'a, V: 'a> VacantEntry<'a, K, V> {
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        let id = self.id;
        let  entry_index = IdMap::<K, V>::mut_entry_index(&mut self.map.table, id);
        assert!(self.map.entries.get_mut(*entry_index as usize).is_none(), "VacantEntry exists!");
        let new_entry = self.map.entries.len() as u32;
        self.map.entries.push((self.key, value));
        *entry_index = new_entry;
        &mut self.map.entries[new_entry as usize].1
    }
    #[inline]
    pub fn or_insert_with<F>(self, func: F) -> &'a mut V where F: FnOnce() -> V {
        self.insert(func())
    }
}
pub struct IntoIter<K, V>(vec::IntoIter<(K, V)>);
impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}
impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}
impl<K: IntegerId, V> IntoIterator for IdMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    #[inline]
    fn into_iter(mut self) -> Self::IntoIter {
        self.table.clear();
        self.table.shrink_to_fit();
        IntoIter(self.entries.into_iter())
    }
}
impl<'a, K: IntegerId + 'a, V: 'a> IntoIterator for &'a IdMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<K: IntegerId, V> Extend<(K, V)> for IdMap<K, V> {
    fn extend<T: IntoIterator<Item=(K, V)>>(&mut self, iter: T) {
        /*
         * Based on the assumption that these are likely new entries,
         * we add everything to the entry array, then go through the table and remove duplicates.
         */
        let entry_start = self.entries.len();
        self.entries.extend(iter);
        let table = &mut self.table;
        for new_index in entry_start..self.entries.len() {
            let id = self.entries[new_index].0.id32();
            let actual_index = Self::mut_entry_index(table, id);
            let existing_index = *actual_index;
            if existing_index != !0 {
                /*
                 * Oops, looks like we have an existing entry.
                 * Swap the new one with the old one, then move the old one to the end to be removed.
                 * It's important we don't just change the index,
                 * since otherwise we'd have to update the entire table.
                 */
                self.entries.swap(existing_index as usize, new_index);
                self.entries.swap_remove(new_index);
            } else {
                *actual_index = new_index as u32;
            }
        }
    }
}
impl<K: IntegerId, V> FromIterator<(K, V)> for IdMap<K, V> {
    #[inline]
    fn from_iter<T>(iterable: T) -> Self where T: IntoIterator<Item=(K, V)> {
        let mut result = IdMap::new();
        result.extend(iterable);
        result
    }
}
impl<'a, K: IntegerId + Clone + 'a, V: Clone + 'a> FromIterator<(&'a K, &'a V)> for IdMap<K, V> {
    #[inline]
    fn from_iter<T>(iterable: T) -> Self where T: IntoIterator<Item=(&'a K, &'a V)> {
        let mut result = IdMap::new();
        result.extend(iterable);
        result
    }
}
impl<'a, K: IntegerId + Clone + 'a, V: Clone + 'a> Extend<(&'a K, &'a V)> for IdMap<K, V> {
    #[inline]
    fn extend<T: IntoIterator<Item=(&'a K, &'a V)>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(|(key, value)| (key.clone(), value.clone())))
    }
}

pub struct Iter<'a, K: IntegerId + 'a, V: 'a>(slice::Iter<'a, (K, V)>);
impl<'a, K: IntegerId + 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    #[inline]
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if let Some(&(ref key, ref value)) = self.0.next() {
            Some((key, value))
        } else {
            None
        }
    }
}
pub struct Keys<'a, K: IntegerId + 'a, V: 'a>(slice::Iter<'a, (K, V)>);
impl<'a, K: IntegerId + 'a, V: 'a> Iterator for Keys<'a, K, V> {
    type Item = &'a K;
    fn next(&mut self) -> Option<&'a K> {
        if let Some(&(ref key, _)) = self.0.next() {
            Some(key)
        } else {
            None
        }
    }
}

pub struct Values<'a, K: IntegerId + 'a, V: 'a>(slice::Iter<'a, (K, V)>);
impl<'a, K: IntegerId + 'a, V: 'a> Iterator for Values<'a, K, V> {
    type Item = &'a V;
    fn next(&mut self) -> Option<&'a V> {
        if let Some(&(_, ref value)) = self.0.next() {
            Some(value)
        } else {
            None
        }
    }
}

pub struct IterMut<'a, K: IntegerId + 'a, V: 'a>(slice::IterMut<'a, (K, V)>);
impl<'a, K: IntegerId + 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    #[inline]
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        if let Some(&mut (ref key, ref mut value)) = self.0.next() {
            Some((key, value))
        } else {
            None
        }
    }
}


/// Support function that panics if an id is invalid
#[doc(hidden)]
#[cold] #[inline(never)]
pub fn _invalid_id(id: u64) -> ! {
    panic!("ID is invalid: {}", id);
}
