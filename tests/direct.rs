#[macro_use]
extern crate idmap;
#[macro_use]
extern crate idmap_derive;
#[allow(unused_extern_crates)]
extern crate serde;
extern crate serde_test;
#[macro_use]
extern crate serde_derive;
extern crate itertools;


use itertools::Itertools;
use serde_test::{Token, assert_tokens};

use idmap::DirectIdMap;
use KnownState::*;

#[test]
fn test_remove() {
    let mut m = important_cities();
    assert_eq!(m.remove(NewMexico), None);
    for state in IMPORTANT_STATES {
        assert_eq!(Some(state.city()), m.remove(state), "{:#?}", m.raw_debug());
    }
    assert_eq!(m.len(), 0);
    assert_eq!(m.remove(NewMexico), None);
    assert_eq!(m.remove(NorthDakota), None);
}

#[test]
fn test_eq() {
    let first = important_cities();
    let second = important_cities().into_iter().rev().collect::<DirectIdMap<_, _>>();

    assert_eq!(first, second);
}

#[test]
fn test_from_iter() {
    let xs = [(California, "San Diego"), (NewYork, "New York"), (Arizona, "Phoenix")];

    let map: DirectIdMap<_, _> = xs.iter().cloned().collect();

    for &(k, v) in &xs {
        assert_eq!(map.get(k), Some(&v));
    }
    check_missing(TINY_STATES, &map);
}

#[test]
fn test_clone() {
    let original = important_cities();
    let cloned = original.clone();
    assert_eq!(original, cloned);
}

#[test]
fn test_index() {
    let map = important_cities();

    for state in IMPORTANT_STATES {
        assert_eq!(map[state], state.city());
    }
}

#[test]
fn test_declaration_order() {
    let map = important_cities();
    let actual_entries = map.iter()
        .map(|(&state, &city)| (state, city))
        .collect::<Vec<_>>();
    let declared_entries = actual_entries.iter()
        .cloned()
        .sorted();
    assert_eq!(actual_entries, declared_entries);
    let reversed_map = actual_entries.iter().rev()
        .cloned()
        .collect::<DirectIdMap<KnownState, &'static str>>();
    let reversed_entries = reversed_map.iter()
        .map(|(&state, &city)| (state, city))
        .collect::<Vec<_>>();
    assert_eq!(reversed_entries, declared_entries);
}

#[test]
#[should_panic]
#[cfg_attr(feature = "cargo-clippy", allow(no_effect))] // It's supposed to panic
fn test_index_nonexistent() {
    let map = important_cities();

    map[NorthDakota];
}

#[test]
fn test_entry_insert() {
    let mut map = important_cities();

    for &state in ALL_STATES {
        let value = *map.entry(state).or_insert_with(|| state.city());
        assert_eq!(value, state.city());
    }
    check_cities(ALL_STATES, &map);
}

#[test]
fn test_extend_ref() {
    let important = important_cities();
    let mut all = DirectIdMap::new_direct();
    all.insert(NewMexico, "Albuquerque");
    all.insert(California, "Cake");
    all.insert(NorthDakota, "Fargo");

    all.extend(&important);

    assert_eq!(all.len(), 5);
    // Updates must remain in declaration order
    assert_eq!(all.iter().nth(1).unwrap(), (&California, &California.city()));
    assert_eq!(all.iter().nth(4).unwrap(), (&NorthDakota, &"Fargo"));
    check_cities(ALL_STATES, &all);
}

#[test]
fn test_retain() {
    let mut map = important_cities();
    map.retain(|&state, _| match state {
        NewYork => false, // New york city is too big!
        California | Arizona => true,
        _ => unreachable!(),
    });
    assert_eq!(map.len(), 2);
    check_cities(&[Arizona, California], &map);
    check_missing(TINY_STATES, &map);
}


/// List the biggest cities in each state except for `NewMexico` and `NorthDakota`,
/// intentionally excluding them to provide a better test case.
fn important_cities() -> DirectIdMap<KnownState, &'static str> {
    // NOTE: Intentionally out of declared order to try and mess things up
    direct_idmap! {
        Arizona => "Phoenix",
        NewYork => "New York City",
        California => "Los Angeles"
    }
}
#[derive(IntegerId, Debug, Copy, Clone, PartialEq, Serialize, Deserialize, Ord, PartialOrd, Eq)]
enum KnownState {
    Arizona,
    California,
    NewMexico,
    NewYork,
    NorthDakota
}
fn check_missing(states: &[KnownState], target: &DirectIdMap<KnownState, &'static str>) {
    for state in states {
        state.check_missing(target);
    }
}
fn check_cities(states: &[KnownState], target: &DirectIdMap<KnownState, &'static str>) {
    for state in states {
        state.check_city(target);
    }
}
static ALL_STATES: &[KnownState] = &[Arizona, California, NewMexico, NewYork, NorthDakota];
// NOTE: Intentionally out of declared order to try and mess things up

static IMPORTANT_STATES: &[KnownState] = &[Arizona, NewYork, California];
static TINY_STATES: &[KnownState] = &[NorthDakota, NewMexico];
impl KnownState {
    fn city(&self) -> &'static str {
        match *self {
            Arizona => "Phoenix",
            California => "Los Angeles",
            NewMexico => "Albuquerque",
            NewYork => "New York City",
            NorthDakota => "Fargo"
        }
    }
    fn check_missing(self, target: &DirectIdMap<KnownState, &'static str>) {
        assert_eq!(target.get(self), None, "Expected no city for {:?}", self);
    }
    fn check_city(self, target: &DirectIdMap<KnownState, &'static str>) {
        assert_eq!(target.get(self), Some(&self.city()), "Unexpected city for {:?}", self);
    }
}

#[test]
fn test_wrapper() {
    let data = direct_idmap! {
        ExampleWrapper(32) => "abc",
        ExampleWrapper(42) => "life",
    };
    assert_eq!(data[ExampleWrapper(32)], "abc");
    assert_eq!(data[ExampleWrapper(42)], "life");
    assert_eq!(data.get(ExampleWrapper(76)), None)
}

#[test]
fn test_struct_wrapper() {
    let data = direct_idmap! {
        ExampleStructWrapper::new(32) => "abc",
        ExampleStructWrapper::new(42) => "life"
    };
    assert_eq!(data[ExampleStructWrapper::new(32)], "abc");
    assert_eq!(data[ExampleStructWrapper::new(42)], "life");
    assert_eq!(data.get(ExampleStructWrapper::new(76)), None)
}

#[derive(IntegerId, Debug, PartialEq)]
struct ExampleWrapper(u16);
#[derive(IntegerId, Debug, PartialEq)]
struct ExampleStructWrapper {
    value: u16
}
impl ExampleStructWrapper {
    #[inline]
    fn new(value: u16) -> Self {
        ExampleStructWrapper { value }
    }
}

#[test]
fn test_serde() {
    macro_rules! state_tokens {
        ($len:expr, $($state:expr => $city:expr),*) => (&[
            Token::Map { len: Some($len) },
            $(
                Token::Enum { name: "KnownState" },
                Token::Str(stringify!($state)),
                Token::Unit,
                Token::BorrowedStr($city),
            )*
            Token::MapEnd
        ]);
    }
    // Remember, DirectIdMap is in _declaration order_
    const EXPECTED_TOKENS: &[Token] = state_tokens!(3,
        Arizona => "Phoenix",
        California => "Los Angeles",
        NewYork => "New York City"
    );
    assert_tokens(&important_cities(), EXPECTED_TOKENS);
}

