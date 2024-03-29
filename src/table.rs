//! The internal table types that can be used to power an `IdMap`.
//!
//! The underlying tables for an [IdMap]
//!
//! User code shouldn't directly interact with these types,
//! unless they're actually using an `IdMap`.
use std::marker::PhantomData;
use std::{iter, slice, mem, vec};
use std::fmt::{self, Debug, Formatter};
use std::ptr::NonNull;

use super::IntegerId;

/// Assigns unique `u32` indexes to each `IntegerId` key,
/// which can be used to modify the behavior and performance of a `DenseEntryTable`.
///
/// Currently the only implementation is `OrderedIdTable`,
/// which preserves ordering by using a `Vec`
///
/// `DenseEntryTable`s need a separate `IdTable` since entries will be stored densely,
/// though a `DirectEntryTable` doesn't need one at all.
pub trait IdTable: Debug + Clone {
    /// Create a new table
    fn new() -> Self;
    /// Create a table, initialized with the specified capacity
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
    /// It is logically equivalent to a `None` result, but kept for performance reasons.
    fn get(&self, key_index: TableIndex) -> Option<TableIndex>;
    /// Get a mutable reference to the index of the specified key
    ///
    /// See also [IdTable::get]
    fn create_mut(&mut self, key_index: TableIndex) -> &mut TableIndex;
    /// Directly set the value of the specified key
    fn set_raw(&mut self, key_index: TableIndex, value: TableIndex);
    /// Clear table
    fn clear(&mut self);
    /// Reserve room in the table for more keys
    fn reserve(&mut self, amount: usize);
}
/// Allows iteration over pointers to all a [IdTable]'s valid entries.
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
///
/// ## Safety
/// The return pointers must be correctly associated with the table
/// for the safe wrappers to yield the correct lifetimes
pub unsafe trait EntryIterable<K, V> {
    /// The type that iterates over this table's pointers
    type Iter: Iterator<Item=(TableIndex, *const (K, V))> + Clone;
    /// Iterate over raw pointers in this table
    ///
    /// ## Safety
    /// The returned pointers must never be used past the lifetime
    /// for which they are actually valid
    unsafe fn unchecked_entries(&self) -> Self::Iter;
}

/// Safely iterates over the entries in a table
pub struct SafeEntries<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V> {
    unchecked_handle: I::Iter,
    /// Actually provides the safety of this iterator by bounding its lifetime
    _marker: PhantomData<&'a I>
}
impl<'a, K, V, I> SafeEntries<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V> {
    /// Safely iterate over the entries in the specified table
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
#[cfg(feature = "nightly")]
unsafe impl<'a, K, V, I> iter::TrustedLen for SafeEntries<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V>, I: iter::TrustedLen {}

impl<'a, K, V, I> Clone for SafeEntries<'a, K, V, I> 
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V> {
    #[inline]
    fn clone(&self) -> Self {
        SafeEntries {
            unchecked_handle: self.unchecked_handle.clone(),
            _marker: PhantomData
        }
    }
}
impl<'a, K: Debug, V: Debug, I> Debug for SafeEntries<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// Safely iterates over the mutable entries in a table
pub struct SafeEntriesMut<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V> {
    unchecked_handle: I::Iter,
    /// Actually provides the safety of this iterator by bounding its lifetime
    _marker: PhantomData<&'a mut I>
}
impl<'a, K, V, I> SafeEntriesMut<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V> {
    #[inline]
    /// Safely iterate over the mutable entries in the specified [EntryIterable]
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
#[cfg(feature = "nightly")]
unsafe impl<'a, K, V, I> iter::TrustedLen for SafeEntriesMut<'a, K, V, I>
    where K: 'a, V: 'a, I: 'a + EntryIterable<K, V>, I: iter::TrustedLen {}

/// An [IdTable] which preserves the ordering of its keys
#[derive(Debug, Clone)]
pub struct OrderedIdTable {
    table: Vec<TableIndex>,
}
impl OrderedIdTable {
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
        crate::utils::fill_bytes(&mut self.table, additional_elements, !0);
        &mut self.table[index]
    }
}
impl IdTable for OrderedIdTable {
    #[inline]
    fn with_capacity(capacity: usize) -> Self {
        OrderedIdTable {
            table: Vec::with_capacity(capacity),
        }
    }
    #[inline]
    fn new() -> Self {
        OrderedIdTable {
            table: Vec::new(),
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
    fn set_raw(&mut self, index: TableIndex, value: TableIndex) {
        self.table[index.unwrap_index() as usize] = value;
    }
}

/// The index of an entry in either `IdTable` or `EntryTable`.
///
/// The marker index `TableIndex::INVALID` is used to indicate missing entries.
#[derive(Copy, Clone, PartialOrd, PartialEq, Eq, Ord)]
pub struct TableIndex(u32);
unsafe impl crate::utils::ArbitraryBytes for TableIndex {}
impl TableIndex {
    /// The special marker index for a missing/invalid entry,
    /// which may be used by a table to indicate that an entry is missing.
    ///
    /// This is used instead of an `Option` for performance reasons,
    /// as it can often be internally folded into a bounds check
    /// which would otherwise need a seperate check.
    pub const INVALID: TableIndex = TableIndex(u32::max_value());
    /// Create a table index corresponding to the specified key
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
    /// Create a table index from the specified value
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
    /// Add the specified value to this index,
    /// panicking on overflow
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


/// Iterate over all the valid ids in a table
pub struct IterValidIds<'a>(slice::Iter<'a, TableIndex>);
impl<'a> Iterator for IterValidIds<'a> {
    type Item = TableIndex;
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        for &index in &mut self.0 {
            if index.is_valid() {
                return Some(index);
            }
        }
        None
    }
}

/// Stores an `IdMap`'s actual entries, which controls the actual behavior of the map.
///
/// There are currently two primary implementations:
/// - `DenseEntryTable` stores the entries more compactly and preserves insertion order,
///   but it needs a separate `IdTable` to map the keys to indexes in the entry list.
/// - `DirectEntryTable` doesn't need any extra `IdTable` book-keeping or indirection in order
///   to associate keys with entries, though it can't preserve ordering and wastes more space
///   when keys are missing. For these reasons, it's not the default though it can be used as an
///   optimization when you know that the key indexes of the entries will be densely packed.
pub trait EntryTable<K: IntegerId, V>: EntryIterable<K, V> + IntoIterator<Item=(K, V)> {
    /// Create a new table
    fn new() -> Self;
    /// Create a new table, initialized to the specified capacity
    fn with_capacity(capacity: usize) -> Self;
    /// If this table is empty
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// The number of entries in the table
    fn len(&self) -> usize;
    /// Get the entry corresponding to the specified key
    fn get(&self, key: &K) -> Option<&V>;
    /// Get a mutable reference to the entry corresponding to the specified key
    fn get_mut(&mut self, key: &K) -> Option<&mut V>;
    /// Insert a value and associate it with the specified key,
    /// returning the previous value
    fn insert(&mut self, key: K, value: V) -> Option<V>;
    /// Insert a value into a vacant slot, returning a reference to the new value
    fn insert_vacant(&mut self, key: K, value: V) -> &mut V;
    /// Remove the value associated with the specified key.
    ///
    /// This potentially disrupts internal ordering
    fn swap_remove(&mut self, key: &K) -> Option<V>;
    /// Retain the specified entries in the map, returning if any indexes changed
    fn retain<F>(&mut self, func: F) where F: FnMut(&K, &mut V) -> bool;
    /// Clear the table
    fn clear(&mut self);
    /// Reserve room for more entries
    fn reserve(&mut self, amount: usize);
    /// Give a value that will debug the table
    fn raw_debug(&self) -> &dyn Debug where K: Debug, V: Debug;
    /// Get the maximum id of the table
    fn max_id(&self) -> Option<u64>;
    /// Clone the table
    fn cloned(&self) -> Self where K: Clone, V: Clone;
}
/// A table which densely stores its entries
///
/// This saves memory over a direct table when the entries are sparse
#[derive(Debug, Clone)]
pub struct DenseEntryTable<K: IntegerId, V, T: IdTable = OrderedIdTable> {
    entries: Vec<(K, V)>,
    table: T
}
impl<K: IntegerId, V, T: IdTable> DenseEntryTable<K, V, T> {
    fn correct_entries(&mut self) {
        self.table.clear();
        for (entry_index, &(ref key, _)) in self.entries.iter().enumerate() {
            *self.table.create_mut(TableIndex::from_key(key)) = TableIndex::from_index(entry_index);
        }
    }
}
impl<K: IntegerId, V, T: IdTable> EntryTable<K, V> for DenseEntryTable<K, V, T> {
    #[inline]
    fn new() -> Self {
        DenseEntryTable {
            entries: Vec::new(),
            table: T::new()
        }
    }

    #[inline]
    fn with_capacity(capacity: usize) -> Self {
        DenseEntryTable {
            entries: Vec::with_capacity(capacity),
            table: T::new()
        }
    }
    #[inline]
    fn len(&self) -> usize {
        self.entries.len()
    }
    #[inline]
    fn get(&self, key: &K) -> Option<&V> {
        self.table.get(TableIndex::from_key(key)).and_then(|entry_index| {
            // Since invalid indexes are u32::max_value they should always be out of bounds
            self.entries.get(entry_index.raw_index() as usize)
                .map(|&(_, ref value)| value)
        })
    }
    #[inline]
    fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        if let Some(entry_index) = self.table.get(TableIndex::from_key(key)) {
            // Since invalid indexes are u32::max_value they should always be out of bounds
            self.entries.get_mut(entry_index.raw_index() as usize)
                .map(|&mut (_, ref mut value)| value)
        } else {
            None
        }
    }
    #[inline]
    fn insert(&mut self, key: K, value: V) -> Option<V> {
        // NOTE: We have to look before we leap to avoid the borrow checker
        let key_index = TableIndex::from_key(&key);
        if let Some(entry_index) = self.table.get(key_index) {
            let entry_index = entry_index.raw_index() as usize;
            if entry_index < self.entries.len() {
                return Some(mem::replace(&mut self.entries[entry_index], (key, value)).1)
            }
        }
        self.insert_vacant(key, value);
        None
    }
    #[inline]
    fn insert_vacant(&mut self, key: K, value: V) -> &mut V {
        /*
         * This is called both by the entry API and insert once they've the index is vacant.
         * It's a fatal bug for the entry to be present, although its completely memory safe
         */
        debug_assert!(self.get(&key).is_none());
        let key_index = TableIndex::from_key(&key);
        let entry_index = TableIndex::from_index(self.entries.len());
        self.entries.push((key, value));
        *self.table.create_mut(key_index) = entry_index;
        &mut self.entries[entry_index.raw_index() as usize].1
    }
    fn swap_remove(&mut self, key: &K) -> Option<V> {
        let key_index = TableIndex::from_key(key);
        if let Some(original_entry_index) = self.table.get(key_index) {
            let original_raw_entry_index = original_entry_index.raw_index() as usize;
            if original_raw_entry_index < self.entries.len() {
                let last_key_index = TableIndex::from_key(&self.entries.last().unwrap().0);
                let last_entry_index = self.entries.len() - 1;
                // We only need to actually swap the entries if it's not the last element
                if original_raw_entry_index != last_entry_index {
                    self.entries.swap(original_raw_entry_index, last_entry_index);
                    self.table.set_raw(last_key_index, original_entry_index);
                }
                let (_, value) = self.entries.pop().unwrap();
                self.table.set_raw(key_index, TableIndex::INVALID);
                return Some(value)
            }
        }
        None
    }
    #[inline]
    fn retain<F>(&mut self, mut func: F) where F: FnMut(&K, &mut V) -> bool {
        let mut changed = false;
        #[cfg(feature = "nightly")]
        {
            // On nightly, we can use efficient drain_filter
            self.entries.drain_filter(|&mut (ref key, ref mut value)| {
                if !func(key, value) {
                    changed = true;
                    true
                } else {
                    false
                }
            });
        }
        #[cfg(not(feature = "nightly"))]
        {
            // On stable, fallback to requiring allocation
            let mut retained = Vec::with_capacity(self.entries.len());
            let old_entries = mem::take(&mut self.entries);
            for (key, mut value) in old_entries {
                if !func(&key, &mut value) {
                    changed = true;
                } else {
                    retained.push((key, value));
                }
            }
            self.entries = retained;
        }
        if changed {
            self.correct_entries()
        }
    }
    #[inline]
    fn clear(&mut self) {
        self.entries.clear();
    }
    #[inline]
    fn reserve(&mut self, amount: usize) {
        self.table.reserve(amount);
        self.entries.reserve(amount);
    }
    #[inline]
    fn raw_debug(&self) -> &dyn Debug where K: Debug, V: Debug {
        self as &dyn Debug
    }
    fn max_id(&self) -> Option<u64> {
        /*
         * Since the entries could be in any order,
         * we have to walk the entire table in order to find the maximum key.
         */
        self.entries.iter().map(|&(ref key, _)| key.id()).max()
    }
    #[inline]
    fn cloned(&self) -> Self where K: Clone, V: Clone {
        self.clone()
    }
}
unsafe impl<K: IntegerId, V, T: IdTable> EntryIterable<K, V> for DenseEntryTable<K, V, T> {
    type Iter = UncheckedDenseEntryIter<K, V>;

    #[inline]
    unsafe fn unchecked_entries(&self) -> Self::Iter {
        assert_ne!(mem::size_of::<(K, V)>(), 0, "Zero sized type!");
        UncheckedDenseEntryIter {
            index: TableIndex(0),
            ptr: NonNull::new_unchecked(self.entries.as_ptr() as *mut _),
            end: NonNull::new_unchecked(self.entries.as_ptr().add(self.entries.len()) as *mut _)
        }
    }
}
impl<K: IntegerId, V, T: IdTable> IntoIterator for DenseEntryTable<K, V, T> {
    type Item = (K, V);
    type IntoIter = vec::IntoIter<(K, V)>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}
/// An unchecked iterator over the pointers in a dense table
#[doc(hidden)]
pub struct UncheckedDenseEntryIter<K: IntegerId, V> {
    index: TableIndex,
    ptr: NonNull<(K, V)>,
    end: NonNull<(K, V)>
}
impl<K: IntegerId, V> Iterator for UncheckedDenseEntryIter<K, V> {
    type Item = (TableIndex, *const (K, V));

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = ((self.end.as_ptr() as usize) - (self.ptr.as_ptr() as usize)) / mem::size_of::<(K, V)>();
        (size, Some(size))
    }
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        assert_ne!(mem::size_of::<(K, V)>(), 0, "Zero sized type!");
        // Based on the slice iterator
        unsafe {
            let ptr = self.ptr.as_ptr();
            let end = self.end.as_ptr();
            if ptr == end {
                None
            } else {
                let index = self.index;
                self.index = TableIndex(index.0 + 1);
                self.ptr = NonNull::new_unchecked(ptr.add(1));
                Some((index, ptr))
            }
        }
    }
}
impl<K: IntegerId, V> iter::FusedIterator for UncheckedDenseEntryIter<K, V> {}
impl<K: IntegerId, V> iter::ExactSizeIterator for UncheckedDenseEntryIter<K, V> {}
#[cfg(feature = "nightly")]
unsafe impl<K: IntegerId, V> iter::TrustedLen for UncheckedDenseEntryIter<K, V> {}
impl<K: IntegerId, V> Clone for UncheckedDenseEntryIter<K, V> {
    #[inline]
    fn clone(&self) -> Self {
        UncheckedDenseEntryIter {
            index: self.index,
            ptr: self.ptr,
            end: self.end
        }
    }
}

/// A entry table that stores in a flat array
///
/// This has very fast `O(1)` access but can waste memory
/// if the entries are sparse
#[derive(Debug, Clone)]
pub struct DirectEntryTable<K: IntegerId, V> {
    entries: Vec<Option<(K, V)>>,
    count: usize,
}
impl<K: IntegerId, V> DirectEntryTable<K, V> {
    #[cold] #[inline(never)]
    fn grow_entries(entries: &mut Vec<Option<(K, V)>>, index: usize) -> &mut Option<(K, V)> {
        assert!(index >= entries.len());
        let additional_elements = index - entries.len() + 1;
        entries.reserve(additional_elements);
        while entries.len() < entries.capacity() {
            entries.push(None);
        }
        assert_eq!(entries.len(), entries.capacity());
        &mut entries[index]
    }
}
impl<K: IntegerId, V> EntryTable<K, V> for DirectEntryTable<K, V> {
    #[inline]
    fn new() -> Self {
        DirectEntryTable {
            entries: Vec::new(),
            count: 0
        }
    }

    #[inline]
    fn with_capacity(capacity: usize) -> Self {
        let mut entries = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            entries.push(None);
        }
        DirectEntryTable {
            entries, count: 0
        }
    }
    #[inline]
    fn len(&self) -> usize {
        debug_assert_eq!(self.count, SafeEntries::new(self).count());
        self.count
    }
    #[inline]
    fn get(&self, key: &K) -> Option<&V> {
        match self.entries.get(key.id32() as usize) {
            Some(&Some((_, ref value))) => Some(value),
            _ => None
        }
    }
    #[inline]
    fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        match self.entries.get_mut(key.id32() as usize) {
            Some(&mut Some((_, ref mut value))) => Some(value),
            _ => None
        }
    }
    #[inline]
    fn insert(&mut self, key: K, value: V) -> Option<V> {
        let raw_index = key.id32() as usize;
        // NOTE: We have to look before we leap to avoid the borrow checker
        let target = if raw_index < self.entries.len() {
            &mut self.entries[raw_index]
        } else {
            Self::grow_entries(&mut self.entries, raw_index)
        };
        if let Some((_, old)) = mem::replace(target, Some((key, value))) {
            Some(old)
        } else {
            self.count += 1;
            None
        }
    }
    #[inline]
    fn insert_vacant(&mut self, key: K, value: V) -> &mut V {
        let index = key.id32() as usize;
        let target = if index < self.entries.len() {
            &mut self.entries[index]
        } else {
            Self::grow_entries(&mut self.entries, index)
        };
        /*
         * This is called by the entry API once they've checked the index is vacant.
         * It's a fatal bug for the entry to be present, although its completely memory safe
         * The assert shouldn't hurt performance, since `Drop` would have to check regardless.
         */
        assert!(target.is_none());
        *target = Some((key, value));
        self.count += 1;
        if let Some((_, ref mut value)) = *target {
            value
        } else {
            unreachable!()
        }
    }
    #[inline]
    fn swap_remove(&mut self, key: &K) -> Option<V> {
        // We have very little to do compared to a `DenseEntryTable`
        let index = key.id32() as usize;
        if let Some(existing) = self.entries.get_mut(index) {
            if let Some((_, old)) = existing.take() {
                self.count -= 1;
                return Some(old)
            }
        }
        None
    }
    #[inline]
    fn retain<F>(&mut self, mut func: F) where F: FnMut(&K, &mut V) -> bool {
        let mut removed = 0;
        for entry in &mut self.entries {
            if let Some((ref key, ref mut value)) = *entry {
                if func(key, value) {
                    continue
                } else {
                    removed += 1;
                }
            }
            *entry = None;
        }
        assert!(self.count >= removed);
        self.count -= removed;
    }
    #[inline]
    fn clear(&mut self) {
        self.entries.clear();
        self.count = 0;
    }
    #[inline]
    fn reserve(&mut self, amount: usize) {
        self.entries.reserve(amount);
    }
    #[inline]
    fn raw_debug(&self) -> &dyn Debug where K: Debug, V: Debug {
        self as &dyn Debug
    }
    #[inline]
    fn max_id(&self) -> Option<u64> {
        /*
         * Since a sparse entry table is guaranteed to be sorted by the id,
         * all we have to do is iterate backwards and find the id of the last entry.
         */
        for back in self.entries.iter().rev() {
            if let Some((ref key, _)) = *back {
                return Some(key.id())
            }
        }
        None
    }
    #[inline]
    fn cloned(&self) -> Self where K: Clone, V: Clone {
        self.clone()
    }
}
unsafe impl<K: IntegerId, V> EntryIterable<K, V> for DirectEntryTable<K, V> {
    type Iter = UncheckedSparseEntryIter<K, V>;

    #[inline]
    unsafe fn unchecked_entries(&self) -> Self::Iter {
        assert_ne!(mem::size_of::<Option<(K, V)>>(), 0, "Zero sized type!");
        UncheckedSparseEntryIter {
            index: TableIndex(0),
            count: self.count,
            ptr: NonNull::new_unchecked(self.entries.as_ptr() as *mut _),
            end: NonNull::new_unchecked(self.entries.as_ptr().add(self.entries.len()) as *mut _)
        }
    }
}
impl<K: IntegerId, V> IntoIterator for DirectEntryTable<K, V> {
    type Item = (K, V);
    type IntoIter = SparseEntryIntoIter<K, V>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        SparseEntryIntoIter(self.entries.into_iter())
    }
}
/// Wraps [std::vec::IntoIter], filtering out missing entries
#[doc(hidden)]
pub struct SparseEntryIntoIter<K, V>(vec::IntoIter<Option<(K, V)>>);
impl<K: IntegerId, V> Iterator for SparseEntryIntoIter<K, V> {
    type Item = (K, V);
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
    #[inline]
    fn next(&mut self) -> Option<(K, V)> {
        'scanLoop: loop {
            return match self.0.next() {
                Some(Some((key, value))) => Some((key, value)),
                Some(None) => continue 'scanLoop,
                None => None
            }
        }
    }
}
impl<K: IntegerId, V> iter::DoubleEndedIterator for SparseEntryIntoIter<K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        'scanLoop: loop {
            return match self.0.next_back() {
                Some(Some((key, value))) => Some((key, value)),
                Some(None) => continue 'scanLoop,
                None => None
            }
        }
    }
}

/// Iterates over the entries in a direct table, filtering out missing entries
#[doc(hidden)]
pub struct UncheckedSparseEntryIter<K: IntegerId, V> {
    index: TableIndex,
    /// How many elements the `SparseEntryTable` claims are actually present.
    ///
    /// Since this claim is produced by possibly buggy safe code,
    /// unsafe code shouldn't rely on and we can't implement `TrustedLen`.
    ///
    /// However, it is perfectly memory-safe to implement `ExactSizeIterator`,
    /// since that's just a hint that unsafe code can't rely upon for memory safety.
    /// A buggy implementation there wouldn't break memory safety,
    /// although it could result in some weird bugs where an 'exact' iterator is wrong.
    count: usize,
    ptr: NonNull<Option<(K, V)>>,
    end: NonNull<Option<(K, V)>>
}
impl<K: IntegerId, V> Iterator for UncheckedSparseEntryIter<K, V> {
    type Item = (TableIndex, *const (K, V));

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        // Remember, this is a 'guess' and unsafe code can't rely on it
        (self.count, Some(self.count))
    }
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        assert_ne!(mem::size_of::<(K, V)>(), 0, "Zero sized type!");
        // Based on the slice iterator
        unsafe {
            while self.ptr.as_ptr() != self.end.as_ptr() {
                let index = self.index;
                let element = self.ptr.as_ptr();
                self.index = TableIndex(index.0 + 1);
                self.ptr = NonNull::new_unchecked(element.add(1));
                if let Some(ref inner) = *element {
                    self.count -= 1;
                    return Some((index, inner))
                }
            }
            None
        }
    }
}
impl<K: IntegerId, V> iter::FusedIterator for UncheckedSparseEntryIter<K, V> {}
impl<K: IntegerId, V> iter::ExactSizeIterator for UncheckedSparseEntryIter<K, V> {}
impl<K: IntegerId, V> Clone for UncheckedSparseEntryIter<K, V> {
    #[inline]
    fn clone(&self) -> Self {
        UncheckedSparseEntryIter {
            index: self.index,
            count: self.count,
            ptr: self.ptr,
            end: self.end
        }
    }
}
