//! Enables serde serialization support for `IdMap`
use std::marker::PhantomData;


use std::fmt::{self, Formatter};
use serde::de::{Deserialize, Deserializer, Visitor, MapAccess};
use serde::ser::{SerializeMap, Serializer, Serialize};

use super::{IdMap, IntegerId};
use super::table::IdTable;

struct IdMapVisitor<K: IntegerId, V, T: IdTable<K, V>>(PhantomData<IdMap<K, V, T>>);

impl<'de, K, V, T> Visitor<'de> for IdMapVisitor<K, V, T>
    where K: IntegerId, T: IdTable<K, V>, K: Deserialize<'de>, V: Deserialize<'de> {
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
    where K: Deserialize<'de>, T: IdTable<K, V>,
          K: IntegerId, V: Deserialize<'de> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_map(IdMapVisitor(PhantomData))
    }
}
impl<K, V, T> Serialize for IdMap<K, V, T>
    where K: IntegerId, K: Serialize, V: Serialize, T: IdTable<K, V> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(self.len()))?;
        for (k, v) in self.iter() {
            map.serialize_entry(k, v)?;
        }
        map.end()
    }   
}
