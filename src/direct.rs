//! Type aliases for [DirectIdMap]

use crate::{IdMap};
use crate::table::DirectEntryTable;

/// An `IdMap` that stores its entries without any indirection,
/// but takes much more space when entries are missing.
///
/// Although this map has slightly less space overhead when most of the entries are present,
/// it has much more space overhead when many entries are missing.
/// Additionally, it's unable to preserve insertion order and the entries are always in declaration order.
/// Iteration is based on the ids of the `IntegerId` keys,
/// and is slower than an `OrderedIdMap` since missing entries have to be manually skipped.
pub type DirectIdMap<K, V> = IdMap<K, V, DirectEntryTable<K, V>>;


/// An iterator over the entries of an [DirectIdMap]
pub type Iter<'a, K, V> = crate::Iter<'a, K, V, DirectEntryTable<K, V>>;

/// An mutable iterator over the entries of an [DirectIdMap]
pub type IterMut<'a, K, V> = crate::IterMut<'a, K, V, DirectEntryTable<K, V>>;

/// An iterator over the keys of an [DirectIdMap]
pub type Keys<'a, K, V> = crate::Keys<'a, K, V, DirectEntryTable<K, V>>;

/// An iterator over the values of an [DirectIdMap]
pub type Values<'a, K, V> = crate::Values<'a, K, V, DirectEntryTable<K, V>>;

/// An mutable iterator over the values of an [DirectIdMap]
pub type ValuesMut<'a, K, V> = crate::ValuesMut<'a, K, V, DirectEntryTable<K, V>>;

/// An entry in an [DirectIdMap]
pub type Entry<'a, K, V> = crate::Entry<'a, K, V, DirectEntryTable<K, V>>;

/// An occupied entry in an [DirectIdMap]
pub type OccupiedEntry<'a, K, V> = crate::OccupiedEntry<'a, K, V, DirectEntryTable<K, V>>;

/// A vacant entry in an [DirectIdMap]
pub type VacantEntry<'a, K, V> = crate::VacantEntry<'a, K, V, DirectEntryTable<K, V>>;
