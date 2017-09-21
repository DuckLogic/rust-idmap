//! Efficient maps of integer id keys to values, backed by an underlying `Vec`.
//! However, unless a `CompactIdMap` is used, space requirements are O(n) the largest key.
//! Any type that implements `IntegerId` can be used for the key,
//! but no storage is wasted if the key can be represented from the id.
#![feature(try_from, nonzero, trusted_len, fused, const_max_value, core_intrinsics)]
extern crate core;
#[cfg(feature="serde")]
extern crate serde;

use std::marker::PhantomData;
use std::iter::{self, FromIterator};
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
    EntryTable, EntryIterable, DenseEntryTable,
    SafeEntries, SafeEntriesMut, DirectEntryTable
};

/// An `IdMap` that stores its entries without any indirection,
/// but takes much more space when entries are missing.
///
/// Although this map has slightly less space overhead when most of the entries are present,
/// it has much more space overhead when many entries are missing.
/// Additionally, it's unable to preserve insertion order and the entries are always in declaration order.
/// Iteration is based on the ids of the `IntegerId` keys,
/// and is slower than an `OrderedIdMap` since missing entries have to be manually skipped.
pub type DirectIdMap<K, V> = IdMap<K, V, DirectEntryTable<K, V>>;

/// The default `IdMap` that preserves insertion order
/// and requires little space when keys have missing entries.
///
/// This is the default way that `IdMap` behaves and is recommended for most users,
/// unless you're really sure that you want a `DirectIdMap`.
///
/// Insertion order is maintained by having an indirection into an entry array like in `OrderMap`.
/// Essentially, it's a `{ table: Vec<u32>, entries: Vec<(K, V) }`,
/// which has little overhead for missing entries.
/// However the indirection makes access slightly slower than a `DirectIdMap`,
/// and requires slightly more overhead than a `DirectIdMap` when entries are actually present.
/// If you aren't worried about the overhead for missing entries, and you want to avoid the indirection
/// you could use a `DirectIdMap` instead.
pub type OrderedIdMap<K, V> = IdMap<K, V, DenseEntryTable<K, V>>;

/// A map of mostly-contiguous `IntegerId` keys to values, backed by a `Vec`.
///
/// This is parametric over the type of the underlying `EntryTable`, which controls its behavior
/// By default it's equivelant to an `OrderedIdMap`,
/// though you can explicitly request a `DirectIdMap` instead.
///
/// From the user's presepctive, this is equivelant to a nice wrapper around a `Vec<Option<(K, V)>>`,
/// that preserves insertion order and saves some space for missing keys.
/// More details on the possible internal representations
/// are documented in the `OrderedIdMap` and `DirectIdMap` aliases.
#[derive(Clone)]
pub struct IdMap<K: IntegerId, V, T: EntryTable<K, V> = DenseEntryTable<K, V>> {
    entries: T,
    marker: PhantomData<DirectEntryTable<K, V>>
}
impl<K: IntegerId, V> IdMap<K, V, DirectEntryTable<K, V>> {
    #[inline]
    pub fn new_direct() -> Self {
        IdMap::new_other()
    }
    #[inline]
    pub fn with_capacity_direct(capacity: usize) -> Self {
        IdMap::with_capacity_other(capacity)
    }
}
impl<K: IntegerId, V> IdMap<K, V> {
    /// Create an empty IdMap using a `DenseEntryTable` and `OrderedIdTable`
    #[inline]
    pub fn new() -> Self {
        IdMap {
            entries: DenseEntryTable::new(),
            marker: PhantomData
        }
    }
    /// Create an IdMap with the specified capacity, using an `OrderedIdTable`
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        IdMap {
            entries: DenseEntryTable::with_capacity(capacity),
            marker: PhantomData
        }
    }
}
impl<K: IntegerId, V, T: EntryTable<K, V>> IdMap<K, V, T> {
    /// Create an empty `IdMap` with a custom entry table type.
    #[inline]
    pub fn new_other() -> Self {
        IdMap {
            entries: T::new(),
            marker: PhantomData
        }
    }
    /// Create a new `IdMap` with the specified capacity but a custom entry table.
    #[inline]
    pub fn with_capacity_other(capacity: usize) -> Self {
        IdMap {
            entries: T::with_capacity(capacity),
            marker: PhantomData
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
        self.entries.max_id()
    }
    #[inline]
    pub fn get<Q: Borrow<K>>(&self, key: Q) -> Option<&V> {
        let key = key.borrow();
        self.entries.get(key)
    }
    #[inline]
    pub fn get_mut<Q: Borrow<K>>(&mut self, key: Q) -> Option<&mut V> {
        let key = key.borrow();
        self.entries.get_mut(key)
    }
    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.entries.insert(key, value)
    }
    #[inline]
    pub fn remove<Q: Borrow<K>>(&mut self, key: Q) -> Option<V> {
        let key = key.borrow();
        self.entries.swap_remove(key)
    }
    #[inline]
    pub fn entry(&mut self, key: K) -> Entry<K, V, T> {
        if self.entries.get(&key).is_some() {
            Entry::Occupied(OccupiedEntry {
                map: self, key
            })
        } else {
            Entry::Vacant(VacantEntry { key, map: self })
        }
    }
    #[inline]
    pub fn iter(&self) -> Iter<K, V, T> {
        Iter(SafeEntries::new(&self.entries))
    }
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<K, V, T> {
        IterMut(SafeEntriesMut::new(&mut self.entries))
    }
    #[inline]
    pub fn keys(&self) -> Keys<K, V, T> {
        Keys(SafeEntries::new(&self.entries))
    }
    #[inline]
    pub fn values(&self) -> Values<K, V, T> {
        Values(SafeEntries::new(&self.entries))
    }
    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<K, V, T> {
        ValuesMut(SafeEntriesMut::new(&mut self.entries))
    }
    #[inline]
    pub fn clear(&mut self) {
        self.entries.clear();
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
        self.entries.retain(func);
    }
    /// Reserve space for the specified number of additional elements
    #[inline]
    pub fn reserve(&mut self, amount: usize) {
        self.entries.reserve(amount);
    }
    /// Give a wrapper that will debug the underlying representation of this `IdMap`
    #[inline]
    pub fn raw_debug(&self) -> RawDebug<K, V, T> where K: Debug, V: Debug {
        RawDebug(self)
    }
}
/// A wrapper to debug the underlying representation of an `IdMap`
pub struct RawDebug<'a, K: IntegerId + 'a, V: 'a, T: 'a + EntryTable<K, V>>(&'a IdMap<K, V, T>);
impl<'a, K, V, T> Debug for RawDebug<'a, K, V, T>
    where K: IntegerId + Debug, V: Debug, T: EntryTable<K, V>, K: 'a, V: 'a, T: 'a {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("IdMap")
            .field("entries", self.0.entries.raw_debug())
            .finish()
    }
}
/// Checks if two have the same contents, ignoring the order.
impl<K, V1, T1, V2, T2> PartialEq<IdMap<K, V2, T2>> for IdMap<K, V1, T1>
    where K: IntegerId, V1: PartialEq<V2>,
          T1: EntryTable<K, V1>, T2: EntryTable<K, V2>, {
    fn eq(&self, other: &IdMap<K, V2, T2>) -> bool {
        if self.entries.len() != other.entries.len() {
            return false;
        }
        self.iter().all(|(key, value)| {
            other.get(key).map_or(false, |other_value| value == other_value)
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
impl<K: IntegerId, V, T: EntryTable<K, V>> Default for IdMap<K, V, T> {
    #[inline]
    fn default() -> Self {
        IdMap::new_other()
    }
}
impl<K: IntegerId, V, T: EntryTable<K, V>> Index<K> for IdMap<K, V, T> {
    type Output = V;
    #[inline]
    fn index(&self, key: K) -> &V {
        &self[&key]
    }
}
impl<K: IntegerId, V, T: EntryTable<K, V>> IndexMut<K> for IdMap<K, V, T> {
    #[inline]
    fn index_mut(&mut self, key: K) -> &mut V {
        &mut self[&key]
    }
}
impl<'a, K: IntegerId, V, T: EntryTable<K, V>> Index<&'a K> for IdMap<K, V, T> {
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
impl<'a, K: IntegerId, V, T: EntryTable<K, V>> IndexMut<&'a K> for IdMap<K, V, T> {
    #[inline]
    fn index_mut(&mut self, key: &'a K) -> &mut V {
        if let Some(value) = self.get_mut(key) {
            value
        } else {
            panic!("Missing entry for {:?}", key)
        }
    }
}
impl<K: IntegerId, V: Debug, T: EntryTable<K, V>> Debug for IdMap<K, V, T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut d = f.debug_map();
        for (key, value) in self.iter() {
            d.entry(key, value);
        }
        d.finish()
    }
}
pub enum Entry<'a, K: IntegerId + 'a, V: 'a, T: 'a + EntryTable<K, V>> {
    Occupied(OccupiedEntry<'a, K, V, T>),
    Vacant(VacantEntry<'a, K, V, T>)
}
impl<'a, K: IntegerId + 'a, V: 'a, T: EntryTable<K, V>> Entry<'a, K, V, T> {
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
pub struct OccupiedEntry<'a, K: IntegerId + 'a, V: 'a, T: 'a + EntryTable<K, V>> {
    map: &'a mut IdMap<K, V, T>,
    key: K,
}
impl<'a, K: IntegerId + 'a, V: 'a, T: EntryTable<K, V>> OccupiedEntry<'a, K, V, T> {
    #[inline]
    pub fn key(&self) -> &K {
        &self.key
    }
    #[inline]
    pub fn value(self) -> &'a mut V {
         self.map.entries.get_mut(&self.key).unwrap()
    }
}
pub struct VacantEntry<'a, K: IntegerId + 'a, V: 'a, T: EntryTable<K, V> + 'a> {
    map: &'a mut IdMap<K, V, T>,
    key: K,
}
impl<'a, K: IntegerId + 'a, V: 'a, T: EntryTable<K, V> + 'a> VacantEntry<'a, K, V, T> {
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        self.map.entries.insert_vacant(self.key, value)
    }
    #[inline]
    pub fn or_insert_with<F>(self, func: F) -> &'a mut V where F: FnOnce() -> V {
        self.insert(func())
    }
}
impl<K: IntegerId, V, T: EntryTable<K, V>> IntoIterator for IdMap<K, V, T> {
    type Item = (K, V);
    type IntoIter = <T as IntoIterator>::IntoIter;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}
impl<'a, K: IntegerId + 'a, V: 'a, T: 'a> IntoIterator for &'a IdMap<K, V, T>
    where T: EntryTable<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V, T>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V, T> IntoIterator for &'a mut IdMap<K, V, T>
    where T: EntryTable<K, V>, K: IntegerId + 'a, V: 'a, T: 'a {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V, T>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
impl<K: IntegerId, V, T: EntryTable<K, V>> Extend<(K, V)> for IdMap<K, V, T> {
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
impl<K: IntegerId, V, T: EntryTable<K, V>> FromIterator<(K, V)> for IdMap<K, V, T> {
    #[inline]
    fn from_iter<I>(iterable: I) -> Self where I: IntoIterator<Item=(K, V)> {
        let mut result = Self::new_other();
        result.extend(iterable);
        result
    }
}
impl<'a, K, V, T> FromIterator<(&'a K, &'a V)> for IdMap<K, V, T>
    where K: IntegerId + Clone + 'a, V: Clone + 'a, T: EntryTable<K, V> {
    #[inline]
    fn from_iter<I>(iterable: I) -> Self where I: IntoIterator<Item=(&'a K, &'a V)> {
        let mut result = Self::new_other();
        result.extend(iterable);
        result
    }
}
impl<'a, K, V, T> Extend<(&'a K, &'a V)> for IdMap<K, V, T>
    where K: IntegerId + Clone + 'a, V: Clone + 'a, T: EntryTable<K, V> {
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
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.0.size_hint()
            }
            #[inline]
            fn next(&mut self) -> Option<$item> {
                let $handle = &mut self.0;
                $next
            }
        }
        impl<$lifetime, $key, $value, I> iter::FusedIterator for $name<$lifetime, $key, $value, I>
            where $key: IntegerId + $lifetime, $value: $lifetime,
                  I: 'a + EntryIterable<$key, $value>, I: iter::FusedIterator {}
        impl<$lifetime, $key, $value, I> iter::ExactSizeIterator for $name<$lifetime, $key, $value, I>
            where $key: IntegerId + $lifetime, $value: $lifetime,
                  I: 'a + EntryIterable<$key, $value>, I: iter::ExactSizeIterator {}
        unsafe impl<$lifetime, $key, $value, I> iter::TrustedLen for $name<$lifetime, $key, $value, I>
            where $key: IntegerId + $lifetime, $value: $lifetime,
                  I: 'a + EntryIterable<$key, $value>, I: iter::TrustedLen {}
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
