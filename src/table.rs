//! The internal table types that can be used to power an `IdMap`.
//!
//! User code shouldn't directly interact with these types,
//! unless they're actually using an `IdMap`.
#![cfg_attr(feature = "cargo-clippy", allow(new_without_default_derive))]
use std::marker::PhantomData;
use std::{iter, slice, mem, vec};
use std::fmt::{self, Debug, Formatter};
use std::intrinsics;

use super::IntegerId;

/// Assigns unique `u32` indexes to each `IntegerId` key,
/// which can be used to modify the behavior and performance of an `IdMap`.
///
/// Currently the three main implementations are:
/// - `OrderedIdTable` is the default which preserves ordering by using a `Vec`
/// - `CompactIdTable` handles indexes that don't start at zero by using a `VecDeque`
/// - `DirectIdTable` is the identity implementation which always uses the keys id as its index,
///   but requires the entry table to be sparse and unordered.
///
/// Both compact and ordered id tables use a `DenseEntryTable` since entries will be stored densely,
/// though a `DirectIdTable` uses a `SparseEntryTable` since some entries may be empty.
pub trait IdTable<K: IntegerId, V> {
    type Entries: EntryTable<K, V>;
    fn new() -> Self;
    fn with_capacity(capacity: usize) -> Self;
    /// Determine the index of the specified key, which may or may not be valid.
    ///
    /// In other words this may have 'false positives',
    /// so that `Some(TableIndex::from(key))` is a correct implementation even though
    /// the index isn't necessarily in-bounds for the entry table.
    /// However, it can never have 'false negatives' so `None` and `Some(TableIndex::INVALID)`
    /// are both wrong.
    ///
    /// The `TableIndex::INVALID` index is special case and should never be considered valid
    /// under any circumstances.
    /// It is logically equivelant to a `None` result, but kept for performance reasons.
    fn get(&self, key: TableIndex) -> Option<TableIndex>;
    fn create_mut(&mut self, target: TableIndex) -> &mut TableIndex;
    fn set_raw(&mut self, target: TableIndex, value: TableIndex);
    fn clear(&mut self);
    fn reserve(&mut self, amount: usize);
    fn raw_debug(&self) -> &Debug where K: Debug, V: Debug;
}
/// Allows iteration over pointers to all a table's valid entries.
///
/// This trait is completely unsafe and has to use raw pointers,
/// since there's currently no way for a trait to express that the iterators
/// it returns are bound to the lifetime of the struct.
///
/// Using the either the iterator or the values it return beyond the lifetime of the reference to
/// the iterable is undefined behavior the compiler can't check your for,
/// so it's recommended to use the safe wrappers `SafeEntries` and `SafeEntriesMut`
///
/// However, it can be safely wrapped in `SafeEntries` and `SafeEntriesMut` traits.
pub unsafe trait EntryIterable<K, V> {
    type Iter: Iterator<Item=(TableIndex, *const (K, V))>;
    unsafe fn unchecked_entries(&self) -> Self::Iter;
}

pub struct SafeEntries<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V> {
    unchecked_handle: I::Iter,
    /// Actually provides the safety of this iterator by bounding its lifetime
    _marker: PhantomData<&'a I>
}
impl<'a, K, V, I> SafeEntries<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V> {
    #[inline]
    pub fn new(iterable: &'a I) -> Self {
        unsafe {
            SafeEntries {
                unchecked_handle: iterable.unchecked_entries(),
                _marker: PhantomData
            }
        }
    }
}
impl<'a, K, V, I> Iterator for SafeEntries<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V> {
    type Item = (TableIndex, &'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.unchecked_handle.next().map(|(index, entry_ptr)| {
            unsafe { (index, &(*entry_ptr).0, &(*entry_ptr).1) }
        })
    }
}
impl<'a, K, V, I> iter::FusedIterator for SafeEntries<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V>, I: iter::FusedIterator {}
impl<'a, K, V, I> iter::ExactSizeIterator for SafeEntries<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V>, I: iter::ExactSizeIterator {}
unsafe impl<'a, K, V, I> iter::TrustedLen for SafeEntries<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V>, I: iter::TrustedLen {}


pub struct SafeEntriesMut<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V> {
    unchecked_handle: I::Iter,
    /// Actually provides the safety of this iterator by bounding its lifetime
    _marker: PhantomData<&'a mut I>
}
impl<'a, K, V, I> SafeEntriesMut<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V> {
    #[inline]
    pub fn new(iterable: &'a mut I) -> Self {
        unsafe {
            SafeEntriesMut {
                unchecked_handle: iterable.unchecked_entries(),
                _marker: PhantomData
            }
        }
    }
}
impl<'a, K, V, I> Iterator for SafeEntriesMut<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V> {
    type Item = (TableIndex, &'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.unchecked_handle.next().map(|(index, entry_ptr)| {
            unsafe { (index, &(*entry_ptr).0, &mut (*(entry_ptr as *mut (K, V))).1) }
        })
    }
}
impl<'a, K, V, I> iter::FusedIterator for SafeEntriesMut<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V>, I: iter::FusedIterator {}
impl<'a, K, V, I> iter::ExactSizeIterator for SafeEntriesMut<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V>, I: iter::ExactSizeIterator {}
unsafe impl<'a, K, V, I> iter::TrustedLen for SafeEntriesMut<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V>, I: iter::TrustedLen {}

/// Allows iteration over all of a table's indexes.
pub trait IndexIterable {
    type ValidIter: Iterator<Item=TableIndex>;
    type RawIter: Iterator<Item=TableIndex>;
    fn valid_indexes(self) -> Self::ValidIter;
    fn raw_indexes(self) -> Self::RawIter;
}

#[derive(Debug)]
pub struct OrderedIdTable<K: IntegerId, V> {
    table: Vec<TableIndex>,
    phantom: PhantomData<DenseEntryTable<K, V>>
}
impl<K: IntegerId, V> OrderedIdTable<K, V> {
    #[cold]
    fn create_entry_grow(&mut self, index: usize) -> &mut TableIndex {
        /*
         * Since the vector doubles the allocation each time we grow anyways,
         * we also fill the vector all the way up to its capacity.
         * This avoids growing very often, and amortizes the growth just like the Vec.
         */
        let len = self.table.len();
        if index >= len {
            self.table.reserve(index - len + 1);
        }
        let additional_elements = self.table.capacity() - len;
        ::utils::fill_bytes(&mut self.table, additional_elements, !0);
        &mut self.table[index]
    }
}
impl<K: IntegerId, V> IdTable<K, V> for OrderedIdTable<K, V> {
    type Entries = DenseEntryTable<K, V>;

    #[inline]
    fn with_capacity(capacity: usize) -> Self {
        OrderedIdTable {
            table: Vec::with_capacity(capacity),
            phantom: PhantomData,
        }
    }
    #[inline]
    fn new() -> Self {
        OrderedIdTable {
            table: Vec::new(),
            phantom: PhantomData
        }
    }
    #[inline]
    fn get(&self, key: TableIndex) -> Option<TableIndex> {
        self.table.get(key.raw_index() as usize).cloned()
    }
    #[inline]
    fn create_mut(&mut self, key: TableIndex) -> &mut TableIndex {
        // NOTE: We must look before we leap to work around the borrow checker
        let index = key.unwrap_index() as usize;
        if index < self.table.len() {
            &mut self.table[index]
        } else {
            self.create_entry_grow(index)
        }
    }

    #[inline]
    fn clear(&mut self) {
        self.table.clear();
    }
    #[inline]
    fn reserve(&mut self, amount: usize) {
        self.table.reserve(amount);
    }
    #[inline]
    fn raw_debug(&self) -> &Debug where K: Debug, V: Debug {
        self as &Debug
    }
    #[inline]
    fn set_raw(&mut self, index: TableIndex, value: TableIndex) {
        self.table[index.unwrap_index() as usize] = value;
    }
}
impl<'a, K: IntegerId, V> IndexIterable for &'a OrderedIdTable<K, V> {
    type ValidIter = IterValidIds<'a>;
    type RawIter = iter::Cloned<slice::Iter<'a, TableIndex>>;


    #[inline]
    fn valid_indexes(self) -> Self::ValidIter {
        IterValidIds(self.table.iter())
    }
    #[inline]
    fn raw_indexes(self) -> Self::RawIter {
        self.table.iter().cloned()
    }
}

/// The index of an entry in either `IdTable` or `EntryTable`.
///
/// The marker index `TableIndex::INVALID` is used to indicate missing entries.
#[derive(Copy, Clone, PartialOrd, PartialEq, Eq, Ord)]
pub struct TableIndex(u32);
unsafe impl ::utils::ArbitraryBytes for TableIndex {}
impl TableIndex {
    /// The special marker index for a missing/invalid entry,
    /// which may be used by a table to indicate that an entry is missing.
    ///
    /// This is used instead of an `Option` for performance reasons,
    /// as it can often be internally folded into a bounds check
    /// which would otherwise need a seperate check.
    pub const INVALID: TableIndex = TableIndex(u32::max_value());
    #[inline]
    pub fn from_key<T: IntegerId>(key: &T) -> Self {
        let id = key.id();
        // Remember, u32::max_value() is the marker
        if id < u64::from(u32::max_value()) {
            TableIndex(id as u32)
        } else {
            id_overflow(key)
        }
    }
    #[inline]
    pub fn from_index(index: usize) -> Self {
        assert!(index < (u32::max_value() as usize), "Invalid index: {}", index);
        TableIndex(index as u32)
    }
    /// Give the underlying value of this index, or `None` if it's invalid.
    #[inline]
    pub fn index(self) -> Option<u32> {
        if self.is_valid() {
            Some(self.0)
        } else {
            None
        }
    }
    /// Unwrap the underlying value of this index, without checking validity in release builds.
    ///
    /// This is completely safe to make this a debug-check since it's already going to be
    /// bounds checked.
    #[inline]
    pub fn unwrap_index(self) -> u32 {
        debug_assert!(self.is_valid());
        self.0
    }

    #[inline]
    pub fn offset(self, amount: u32) -> Self {
        if self.0 < (u32::max_value() - amount) {
            let result = TableIndex(self.0 + amount);
            debug_assert!(result.is_valid());
            result
        } else {
            self.offset_failed(amount)
        }
    }
    #[cold] #[inline(never)]
    fn offset_failed(self, amount: u32) -> ! {
        panic!("Unable to offset {:?} by {}", self, amount)
    }

    /// Give the internal value of this index, even if it's invalid.
    #[inline]
    pub fn raw_index(self) -> u32 {
        self.0
    }
    /// Check if the index is valid and not equal to `TableIndex::INVALID`
    #[inline]
    pub fn is_valid(self) -> bool {
        self.0 != u32::max_value()
    }
}
impl Debug for TableIndex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if let Some(index) = self.index() {
            write!(f, "TableIndex({})", index)
        } else {
            write!(f, "TableIndex::INVALID")
        }
    }
}

#[inline(never)]
#[cold]
fn id_overflow<T: IntegerId>(key: &T) -> ! {
    panic!("ID overflowed, {} >= {} for {:?}", key.id(), u32::max_value(), key)
}


pub struct IterValidIds<'a>(slice::Iter<'a, TableIndex>);
impl<'a> Iterator for IterValidIds<'a> {
    type Item = TableIndex;
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(&index) = self.0.next() {
            if index.is_valid() {
                return Some(index);
            }
        }
        None
    }
}

/// Stores an `IdMap`'s entries based on `u32` indexes.
pub trait EntryTable<K: IntegerId, V>: EntryIterable<K, V> + IntoIterator<Item=(K, V)> {
    fn new() -> Self;
    fn with_capacity(capacity: usize) -> Self;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    fn len(&self) -> usize;
    fn get(&self, index: TableIndex) -> Option<&V>;
    fn get_mut(&mut self, index: TableIndex) -> Option<&mut V>;
    fn insert(&mut self, index: &mut TableIndex, key: K, value: V) -> Option<V>;
    fn insert_vacant(&mut self, index: &mut TableIndex, key: K, value: V) -> &mut V;
    fn swap_remove<T: IdTable<K, V>>(&mut self, target_entry: TableIndex, table: &mut T) -> Option<V>;
    fn retain<F>(&mut self, func: F) -> bool where F: FnMut(&K, &V) -> bool;
    fn clear(&mut self);
    fn reserve(&mut self, amount: usize);
    fn raw_debug(&self) -> &Debug where K: Debug, V: Debug;
}
#[derive(Debug)]
pub struct DenseEntryTable<K: IntegerId, V> {
    entries: Vec<(K, V)>
}
impl<K: IntegerId, V> EntryTable<K, V> for DenseEntryTable<K, V> {
    #[inline]
    fn new() -> Self {
        DenseEntryTable {
            entries: Vec::new()
        }
    }

    #[inline]
    fn with_capacity(capacity: usize) -> Self {
        DenseEntryTable {
            entries: Vec::with_capacity(capacity)
        }
    }
    #[inline]
    fn len(&self) -> usize {
        self.entries.len()
    }
    #[inline]
    fn get(&self, index: TableIndex) -> Option<&V> {
        // Since invalid indexes are u32::max_value they should always be out of bounds
        self.entries.get(index.raw_index() as usize)
            .map(|&(_, ref value)| value)
    }
    #[inline]
    fn get_mut(&mut self, index: TableIndex) -> Option<&mut V> {
        self.entries.get_mut(index.raw_index() as usize)
            .map(|&mut (_, ref mut value)| value)
    }
    #[inline]
    fn insert(&mut self, target_index: &mut TableIndex, key: K, value: V) -> Option<V> {
        // NOTE: We have to look before we leap to avoid the borrow checker
        let raw_index = target_index.raw_index() as usize;
        if self.entries.get(raw_index).is_some() {
            Some(mem::replace(&mut self.entries[raw_index], (key, value)).1)
        } else {
            self.insert_vacant(target_index, key, value);
            None
        }
    }
    #[inline]
    fn insert_vacant(&mut self, target_index: &mut TableIndex, key: K, value: V) -> &mut V {
        /*
         * This is called both by the entry API and insert once they've the index is vacant.
         * It's a fatal bug for the entry to be present, although its completely memory safe
         */
        debug_assert!(self.get(*target_index).is_none());
        let index = TableIndex::from_index(self.entries.len());
        self.entries.push((key, value));
        *target_index = index;
        &mut self.entries[index.raw_index() as usize].1
    }
    fn swap_remove<T: IdTable<K, V>>(&mut self, original_entry: TableIndex, table: &mut T) -> Option<V> {
        if let Some(original_key_index) = self.entries.get(original_entry.raw_index() as usize)
            .map(|&(ref key, _)| TableIndex::from_key(key)) {
            let original_entry_index = original_entry.raw_index() as usize;
            assert!(!self.entries.is_empty());
            let last_key_index = TableIndex::from_key(&self.entries.last().unwrap().0);
            let last_entry_index = self.entries.len() - 1;
            // We only need to actually swap the entries if it's not the last element
            if original_entry_index != last_entry_index {
                assert!(original_entry_index < self.entries.len());
                self.entries.swap(original_entry_index, last_entry_index);
                table.set_raw(last_key_index, original_entry);
            }
            let (_, value) = self.entries.pop().unwrap();
            table.set_raw(original_key_index, TableIndex::INVALID);
            Some(value)
        } else {
            None
        }
    }
    #[inline]
    fn retain<F>(&mut self, mut func: F) -> bool where F: FnMut(&K, &V) -> bool {
        let mut changed = false;
        self.entries.retain(|&(ref key, ref value)| {
            if func(key, value) {
                changed = true;
                true
            } else {
                false
            }
        });
        changed
    }
    #[inline]
    fn clear(&mut self) {
        self.entries.clear();
    }
    #[inline]
    fn reserve(&mut self, amount: usize) {
        self.entries.reserve(amount);
    }
    #[inline]
    fn raw_debug(&self) -> &Debug where K: Debug, V: Debug {
        self as &Debug
    }
}
unsafe impl<K: IntegerId, V> EntryIterable<K, V> for DenseEntryTable<K, V> {
    type Iter = UncheckedDenseEntryIter<K, V>;

    #[inline]
    unsafe fn unchecked_entries(&self) -> Self::Iter {
        assert_ne!(mem::size_of::<(K, V)>(), 0, "Zero sized type!");
        UncheckedDenseEntryIter {
            index: TableIndex(0),
            ptr: self.entries.as_ptr(),
            end: self.entries.as_ptr().offset(self.entries.len() as isize)
        }
    }
}
impl<K: IntegerId, V> IntoIterator for DenseEntryTable<K, V> {
    type Item = (K, V);
    type IntoIter = vec::IntoIter<(K, V)>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}
pub struct UncheckedDenseEntryIter<K: IntegerId, V> {
    index: TableIndex,
    ptr: *const (K, V),
    end: *const (K, V)
}
impl<K: IntegerId, V> Iterator for UncheckedDenseEntryIter<K, V> {
    type Item = (TableIndex, *const (K, V));

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = ((self.end as usize) - (self.ptr as usize)) / mem::size_of::<(K, V)>();
        (size, Some(size))
    }
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        assert_ne!(mem::size_of::<(K, V)>(), 0, "Zero sized type!");
        // Based on the slice iterator
        unsafe {
            intrinsics::assume(!self.ptr.is_null());
            intrinsics::assume(!self.end.is_null());
            if self.ptr == self.end {
                None
            } else {
                let index = self.index;
                let element = self.ptr;
                self.index = TableIndex(index.0 + 1);
                self.ptr = element.offset(1);
                Some((index, element))
            }
        }
    }
}
impl<K: IntegerId, V> iter::FusedIterator for UncheckedDenseEntryIter<K, V> {}
impl<K: IntegerId, V> iter::ExactSizeIterator for UncheckedDenseEntryIter<K, V> {}
unsafe impl<K: IntegerId, V> iter::TrustedLen for UncheckedDenseEntryIter<K, V> {}
