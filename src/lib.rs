//! Efficient maps of integer id keys to values, backed by an underlying `Vec`.
//! However, unless a `CompactIdMap` is used, space requirements are O(n) the largest key.
//! Any type that implements `IntegerId` can be used for the key,
//! but no storage is wasted if the key can be represented from the id.
#![feature(try_from, nonzero, trusted_len, fused, const_max_value, core_intrinsics)]
extern crate core;
extern crate itertools;
#[cfg(feature="serde")]
extern crate serde;

use std::iter::FromIterator;
use std::borrow::Borrow;
use std::ops::{Index, IndexMut};
use std::fmt::{self, Debug, Formatter};

pub mod table;
#[cfg(feature="serde")]
mod serialization;
mod utils;
mod integer_id;

pub use integer_id::IntegerId;
use table::{
    IdTable, EntryTable, EntryIterable, OrderedIdTable, TableIndex, DenseEntryTable,
    IndexIterable, SafeEntries, SafeEntriesMut
};

use itertools::Itertools;
use itertools::EitherOrBoth::*;

/// A map of mostly-contiguous `IntegerId` keys to values, backed by a `Vec`.
///
/// This is parametric over the type of the underlying `IdTable`, which controls its behavior
/// By default it uses `OrderedIdTable` so insertion order is maintained and
/// indexes are stored starting at zero.
/// However, this means a map with keys `[1000, 10001, 1003]` would allocate 1004 table entries!
/// Therefore `CompactIdMap` should be used if your indexes may start significantly later zero,
/// although it's noticeably slower in the general case.
///
/// Insertion order is maintained, as there's an indirection into an entry array like in `OrderMap`.
/// Therefore, entries which aren't present take less space, as they only need to store the index.
/// If you don't need this and are sure your keys are going to be dense you could use a `DirectIdMap`
/// instead of this to avoid some indirection.
#[derive(Clone)]
pub struct IdMap<K: IntegerId, V, T: IdTable<K, V> = OrderedIdTable<K, V>> {
    table: T,
    entries: T::Entries
}
impl<K: IntegerId, V> IdMap<K, V> {
    /// Create an empty IdMap using an `OrderedIdTable`
    #[inline]
    pub fn new() -> Self {
        IdMap {
            table: OrderedIdTable::new(),
            entries: DenseEntryTable::new()
        }
    }
    /// Create an IdMap with the specified capacity, using an `OrderedIdTable`
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        IdMap {
            table: OrderedIdTable::with_capacity(capacity),
            entries: DenseEntryTable::with_capacity(capacity)
        }
    }
}
impl<K: IntegerId, V, T: IdTable<K, V>> IdMap<K, V, T> {
    /// Create an empty `IdMap` with a custom table type.
    #[inline]
    pub fn new_other() -> Self {
        IdMap {
            table: T::new(),
            entries: T::Entries::new()
        }
    }
    /// Create a new `IdMap` with the specified capacity but a custom table type
    #[inline]
    pub fn with_capacity_other(capacity: usize) -> Self {
        IdMap {
            table: T::with_capacity(capacity),
            entries: T::Entries::with_capacity(capacity)
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
    pub fn max_id(&self) -> Option<u64>  {
        self.keys().map(IntegerId::id).max()
    }
    #[inline]
    pub fn get<Q: Borrow<K>>(&self, key: Q) -> Option<&V> {
        let key = key.borrow();
        if let Some(index) = self.table.get(TableIndex::from_key(key)) {
            self.entries.get(index)
        } else {
            None
        }
    }
    #[inline]
    pub fn get_mut<Q: Borrow<K>>(&mut self, key: Q) -> Option<&mut V> {
        let key = key.borrow();
        if let Some(index) = self.table.get(TableIndex::from_key(key)) {
            self.entries.get_mut(index)
        } else {
            None
        }
    }
    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let entry = self.table.create_mut(TableIndex::from_key(&key));
        self.entries.insert(entry, key, value)
    }
    #[inline]
    pub fn remove<Q: Borrow<K>>(&mut self, key: Q) -> Option<V> {
        let key = key.borrow();
        if let Some(entry_index) = self.table.get(TableIndex::from_key(key)) {
            self.entries.swap_remove(entry_index, &mut self.table)
        } else {
            None
        }
    }
    #[inline]
    pub fn entry(&mut self, key: K) -> Entry<K, V, T> {
        if let Some(entry_index) = self.table.get(TableIndex::from_key(&key)) {
            if self.entries.get(entry_index).is_some() {
                return Entry::Occupied(OccupiedEntry {
                    map: self, key, entry_index
                })
            }
        }
        Entry::Vacant(VacantEntry { key, map: self })
    }
    #[inline]
    pub fn iter(&self) -> Iter<K, V, T::Entries> {
        Iter(SafeEntries::new(&self.entries))
    }
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<K, V, T::Entries> {
        IterMut(SafeEntriesMut::new(&mut self.entries))
    }
    #[inline]
    pub fn keys(&self) -> Keys<K, V, T::Entries> {
        Keys(SafeEntries::new(&self.entries))
    }
    #[inline]
    pub fn values(&self) -> Values<K, V, T::Entries> {
        Values(SafeEntries::new(&self.entries))
    }
    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<K, V, T::Entries> {
        ValuesMut(SafeEntriesMut::new(&mut self.entries))
    }
    #[inline]
    pub fn clear(&mut self) {
        self.entries.clear();
        self.table.clear();
    }
    /// Retains only the elements specified by the predicate.
    /// ```
    /// # use idmap::VecMap;
    /// let mut map: IdMap<usize> = (0..8).map(|x|(x, x*10)).collect();
    /// map.retain(|k, _| k % 2 == 0);
    /// assert_eq!(map.into_iter().collect(), vec![(0, 0), (2, 20), (4, 40), (6, 60)]);
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, func: F) where F: FnMut(&K, &V) -> bool {
        if self.entries.retain(func) {
            self.correct_entries();
        }
    }
    /// Reserve space for the specified number of additional elements
    #[inline]
    pub fn reserve(&mut self, amount: usize) {
        self.table.reserve(amount);
        self.entries.reserve(amount);
    }
    fn correct_entries(&mut self) {
        self.table.clear();
        for (index, key, _) in SafeEntries::new(&self.entries) {
            *self.table.create_mut(TableIndex::from_key(key)) = index;
        }
    }
    /// Give a wrapper that will debug the underlying representation of this `IdMap`
    #[inline]
    pub fn raw_debug(&self) -> RawDebug<K, V, T> where K: Debug, V: Debug {
        RawDebug(self)
    }
}
/// A wrapper to debug the underlying representation of an `IdMap`
pub struct RawDebug<'a, K: IntegerId + 'a, V: 'a, T: 'a + IdTable<K, V>>(&'a IdMap<K, V, T>);
impl<'a, K, V, T> Debug for RawDebug<'a, K, V, T>
    where K: IntegerId + Debug, V: Debug, T: IdTable<K, V>, K: 'a, V: 'a, T: 'a {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("IdMap")
            .field("entries", self.0.entries.raw_debug())
            .field("table", self.0.table.raw_debug())
            .finish()
    }
}
/// Checks if two have the same contents, ignoring the order.
impl<K, V1, T1, V2, T2> PartialEq<IdMap<K, V2, T2>> for IdMap<K, V1, T1>
    where K: IntegerId, V1: PartialEq<V2>,
          T1: IdTable<K, V1>, T2: IdTable<K, V2>,
          for <'a> &'a T1: IndexIterable,
          for <'a> &'a T2: IndexIterable {
    fn eq(&self, other: &IdMap<K, V2, T2>) -> bool {
        /*
         * Since we can't rely on the ordering,
         * we have to check the lookup tables first to find each map's entry.
         */
        if self.entries.len() != other.entries.len() {
            return false;
        }
        self.table.raw_indexes().zip_longest(other.table.raw_indexes()).all(|zip| {
            match zip {
                Both(self_entry_index, other_entry_index) => {
                    match (self.entries.get(self_entry_index), other.entries.get(other_entry_index)) {
                        (Some(first), Some(second)) => first == second,
                        (None, None) => true,
                        _ => false
                    }
                },
                Left(entry_index) | Right(entry_index) => {
                    self.entries.get(entry_index).is_none()
                }
            }
        })
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
pub enum Entry<'a, K: IntegerId + 'a, V: 'a, T: 'a + IdTable<K, V>> {
    Occupied(OccupiedEntry<'a, K, V, T>),
    Vacant(VacantEntry<'a, K, V, T>)
}
impl<'a, K: IntegerId + 'a, V: 'a, T: IdTable<K, V>> Entry<'a, K, V, T> {
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
pub struct OccupiedEntry<'a, K: IntegerId + 'a, V: 'a, T: 'a + IdTable<K, V>> {
    map: &'a mut IdMap<K, V, T>,
    key: K,
    entry_index: TableIndex
}
impl<'a, K: IntegerId + 'a, V: 'a, T: IdTable<K, V>> OccupiedEntry<'a, K, V, T> {
    #[inline]
    pub fn key(&self) -> &K {
        &self.key
    }
    #[inline]
    pub fn value(self) -> &'a mut V {
         self.map.entries.get_mut(self.entry_index).unwrap()
    }
}
pub struct VacantEntry<'a, K: IntegerId + 'a, V: 'a, T: IdTable<K, V> + 'a> {
    map: &'a mut IdMap<K, V, T>,
    key: K,
}
impl<'a, K: IntegerId + 'a, V: 'a, T: IdTable<K, V> + 'a> VacantEntry<'a, K, V, T> {
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        let entry = self.map.table.create_mut(TableIndex::from_key(&self.key));
        self.map.entries.insert_vacant(entry, self.key, value)
    }
    #[inline]
    pub fn or_insert_with<F>(self, func: F) -> &'a mut V where F: FnOnce() -> V {
        self.insert(func())
    }
}
impl<K: IntegerId, V, T: IdTable<K, V>> IntoIterator for IdMap<K, V, T> {
    type Item = (K, V);
    type IntoIter = <T::Entries as IntoIterator>::IntoIter;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}
impl<'a, K: IntegerId + 'a, V: 'a, T: 'a> IntoIterator for &'a IdMap<K, V, T>
    where T: IdTable<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V, T::Entries>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V, T> IntoIterator for &'a mut IdMap<K, V, T>
    where T: IdTable<K, V>, K: IntegerId + 'a, V: 'a, T: 'a {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V, T::Entries>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
impl<K: IntegerId, V, T: IdTable<K, V>> Extend<(K, V)> for IdMap<K, V, T> {
    fn extend<I: IntoIterator<Item=(K, V)>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        if let Some(size) = iter.size_hint().1 {
            self.reserve(size);
        }
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}
impl<K: IntegerId, V, T: IdTable<K, V>> FromIterator<(K, V)> for IdMap<K, V, T> {
    #[inline]
    fn from_iter<I>(iterable: I) -> Self where I: IntoIterator<Item=(K, V)> {
        let mut result = Self::new_other();
        result.extend(iterable);
        result
    }
}
impl<'a, K, V, T> FromIterator<(&'a K, &'a V)> for IdMap<K, V, T>
    where K: IntegerId + Clone + 'a, V: Clone + 'a, T: IdTable<K, V> {
    #[inline]
    fn from_iter<I>(iterable: I) -> Self where I: IntoIterator<Item=(&'a K, &'a V)> {
        let mut result = Self::new_other();
        result.extend(iterable);
        result
    }
}
impl<'a, K, V, T> Extend<(&'a K, &'a V)> for IdMap<K, V, T>
    where K: IntegerId + Clone + 'a, V: Clone + 'a, T: IdTable<K, V> {
    #[inline]
    fn extend<I: IntoIterator<Item=(&'a K, &'a V)>>(&mut self, iter: I) {
        self.extend(iter.into_iter().map(|(key, value)| (key.clone(), value.clone())))
    }
}

macro_rules! delegating_iter {
    ($name:ident, $target:ident, $lifetime:tt, $key:tt, $value:tt, [ $item:ty ], |$handle:ident| $next:expr) => {
        pub struct $name<$lifetime, $key, $value, I>($target<$lifetime, $key, $value, I>)
            where $key: IntegerId + $lifetime, $value: $lifetime, I: 'a + EntryIterable<$key, $value>;
        impl<$lifetime, $key, $value, I> Iterator for $name<$lifetime, $key, $value, I>
            where $key: IntegerId + $lifetime, $value: $lifetime, I: 'a + EntryIterable<$key, $value> {
            type Item = $item;
            #[inline]
            fn next(&mut self) -> Option<$item> {
                let $handle = &mut self.0;
                $next
            }
        }
    };
}
delegating_iter!(Iter, SafeEntries, 'a, K, V, [ (&'a K, &'a V) ], |handle| handle.next().map(|(_, key, value)| (key, value)));
delegating_iter!(IterMut, SafeEntriesMut, 'a, K, V, [ (&'a K, &'a mut V) ], |handle| handle.next().map(|(_, key, value)| (key, value)));
delegating_iter!(Keys, SafeEntries, 'a, K, V, [ &'a K ], |handle| handle.next().map(|(_, key, _)| key));
delegating_iter!(Values, SafeEntries, 'a, K, V, [ &'a V ], |handle| handle.next().map(|(_, _, value)| value));
delegating_iter!(ValuesMut, SafeEntriesMut, 'a, K, V, [ &'a mut V ], |handle| handle.next().map(|(_, _, value)| value));


/// Support function that panics if an id is invalid
#[doc(hidden)]
#[cold] #[inline(never)]
pub fn _invalid_id(id: u64) -> ! {
    panic!("ID is invalid: {}", id);
}
