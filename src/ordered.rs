//! Type aliases for [OrderedIdMap]

use crate::IdMap;
use crate::table::DenseEntryTable;

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

/// An iterator over the entries of an [OrderedIdMap]
pub type Iter<'a, K, V> = crate::Iter<'a, K, V, DenseEntryTable<K, V>>;

/// An mutable iterator over the entries of an [OrderedIdMap]
pub type IterMut<'a, K, V> = crate::IterMut<'a, K, V, DenseEntryTable<K, V>>;

/// An iterator over the keys of an [OrderedIdMap]
pub type Keys<'a, K, V> = crate::Keys<'a, K, V, DenseEntryTable<K, V>>;

/// An iterator over the values of an [OrderedIdMap]
pub type Values<'a, K, V> = crate::Values<'a, K, V, DenseEntryTable<K, V>>;

/// An mutable iterator over the values of an [OrderedIdMap]
pub type ValuesMut<'a, K, V> = crate::ValuesMut<'a, K, V, DenseEntryTable<K, V>>;

/// An entry in an [OrderedIdMap]
pub type Entry<'a, K, V> = crate::Entry<'a, K, V, DenseEntryTable<K, V>>;

/// An occupied entry in an [OrderedIdMap]
pub type OccupiedEntry<'a, K, V> = crate::OccupiedEntry<'a, K, V, DenseEntryTable<K, V>>;

/// A vacant entry in an [OrderedIdMap]
pub type VacantEntry<'a, K, V> = crate::VacantEntry<'a, K, V, DenseEntryTable<K, V>>;

