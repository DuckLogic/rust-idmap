//! Enables serde serialization support for `IdMap`
use std::marker::PhantomData;


use std::fmt::{self, Formatter};
use serde::de::{Deserialize, Deserializer, Visitor, MapAccess};
use serde::ser::{SerializeMap, Serializer, Serialize};

use super::{IdMap, IntegerId};

struct IdMapVisitor<K: IntegerId, V>(PhantomData<IdMap<K, V>>);

impl<'de, K, V> Visitor<'de> for IdMapVisitor<K, V>
    where K: IntegerId, K: Deserialize<'de>, V: Deserialize<'de> {
    type Value = IdMap<K, V>;
    #[inline]
    fn expecting(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("a IdMap")
    }
    #[inline]
    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error> where M: MapAccess<'de> {
        let mut result = IdMap::with_capacity(access.size_hint().unwrap_or(0));
        while let Some((key, value)) = access.next_entry()? {
            result.insert(key, value);
        }
        Ok(result)
    }
}
impl<'de, K, V> Deserialize<'de> for IdMap<K, V>
    where K: Deserialize<'de>, K :IntegerId, V: Deserialize<'de> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_map(IdMapVisitor(PhantomData))
    }
}
impl<K, V> Serialize for IdMap<K, V> 
    where K: IntegerId, K: Serialize, V: Serialize {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(self.len()))?;
        for (k, v) in self {
            map.serialize_entry(k, v)?;
        }
        map.end()
    }   
}
