//! Enables serde serialization support for `IdMap`
use std::marker::PhantomData;


use std::fmt::{self, Formatter};
use serde::de::{Deserialize, Deserializer, Visitor, SeqAccess, MapAccess};
use serde::ser::{SerializeMap, SerializeSeq, Serializer, Serialize};

use super::{IdMap, IdSet, IntegerId};
use super::table::EntryTable;

struct IdMapVisitor<K: IntegerId, V, T: EntryTable<K, V>>(PhantomData<IdMap<K, V, T>>);

impl<'de, K, V, T> Visitor<'de> for IdMapVisitor<K, V, T>
    where K: IntegerId, T: EntryTable<K, V>, K: Deserialize<'de>, V: Deserialize<'de> {
    type Value = IdMap<K, V, T>;
    #[inline]
    fn expecting(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("an IdMap")
    }
    #[inline]
    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error> where M: MapAccess<'de> {
        let mut result = IdMap::with_capacity_other(
            access.size_hint().unwrap_or(0)
        );
        while let Some((key, value)) = access.next_entry()? {
            result.insert(key, value);
        }
        Ok(result)
    }
}
impl<'de, K, V, T> Deserialize<'de> for IdMap<K, V, T>
    where K: Deserialize<'de>, T: EntryTable<K, V>,
          K: IntegerId, V: Deserialize<'de> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_map(IdMapVisitor(PhantomData))
    }
}
impl<K, V, T> Serialize for IdMap<K, V, T>
    where K: IntegerId, K: Serialize, V: Serialize, T: EntryTable<K, V> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(self.len()))?;
        for (k, v) in self.iter() {
            map.serialize_entry(k, v)?;
        }
        map.end()
    }   
}

struct IdSetVisitor<T: IntegerId>(PhantomData<IdSet<T>>);

impl<'de, T> Visitor<'de> for IdSetVisitor<T> where T: IntegerId + Deserialize<'de> {
    type Value = IdSet<T>;
    #[inline]
    fn expecting(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("an IdSet")
    }
    #[inline]
    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error> where
        A: SeqAccess<'de>, {
        let mut result = IdSet::with_capacity(
            seq.size_hint().unwrap_or(0)
        );
        while let Some(element) = seq.next_element::<T>()? {
            result.insert(element);
        }
        Ok(result)
    }
}
impl<'de, T> Deserialize<'de> for IdSet<T>
    where T: IntegerId + Deserialize<'de> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_seq(IdSetVisitor(PhantomData))
    }
}
impl<T> Serialize for IdSet<T>
    where T: IntegerId + Serialize {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for value in self.iter() {
            seq.serialize_element(&value)?;
        }
        seq.end()
    }
}

