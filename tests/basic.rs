#[macro_use]
extern crate idmap;
#[macro_use]
extern crate idmap_derive;
extern crate serde;
extern crate serde_test;
#[macro_use]
extern crate serde_derive;

use serde_test::{Token, assert_tokens};

use idmap::IdMap;
use KnownState::*;

#[test]
fn test_remove() {
    let mut m = important_cities();
    for state in IMPORTANT_STATES {
        assert_eq!(state.city(), m.remove(state).unwrap());
    }
    assert_eq!(m.len(), 0);
    assert_eq!(m.remove(NewMexico), None);
    assert_eq!(m.remove(NorthDakota), None);
}

#[test]
fn test_eq() {
    let first = important_cities();
    let second = important_cities().into_iter().rev().collect::<IdMap<_, _>>();

    assert_eq!(first, second);
}

#[test]
fn test_from_iter() {
    let xs = [(California, "San Diego"), (NewYork, "New York"), (Arizona, "Phoenix")];

    let map: IdMap<_, _> = xs.iter().cloned().collect();

    for &(k, v) in &xs {
        assert_eq!(map.get(k), Some(&v));
    }
    check_missing(TINY_STATES, &map);
}

#[test]
fn test_index() {
    let map = important_cities();

    for state in IMPORTANT_STATES {
        assert_eq!(map[state], state.city());
    }
}

#[test]
#[should_panic]
#[allow(no_effect)] // It's supposed to panic
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
    let mut all = IdMap::new();
    all.insert(NewMexico, "Albuquerque");
    all.insert(NorthDakota, "Fargo");

    all.extend(&important);

    assert_eq!(all.len(), 5);
    assert_eq!(*all.keys().next().unwrap(), NewMexico);
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
    check_cities(&[Arizona, California], &map);
    check_missing(TINY_STATES, &map);
}


/// List the biggest cities in each state except for `NewMexico` and `NorthDakota`,
/// intentionally excluding them to provide a better test case.
fn important_cities() -> IdMap<KnownState, &'static str> {
    idmap! {
        Arizona => "Phoenix",
        California => "Los Angeles",
        NewYork => "New York City"
    }
}
#[derive(IntegerId, Debug, Copy, Clone, PartialEq, Serialize, Deserialize)]
enum KnownState {
    Arizona,
    California,
    NewMexico,
    NewYork,
    NorthDakota
}
fn check_missing(states: &[KnownState], target: &IdMap<KnownState, &'static str>) {
    for state in states {
        state.check_missing(target);
    }
}
fn check_cities(states: &[KnownState], target: &IdMap<KnownState, &'static str>) {
    for state in states {
        state.check_city(target);
    }
}
static ALL_STATES: &[KnownState] = &[Arizona, California, NewMexico, NewYork, NorthDakota];
static IMPORTANT_STATES: &[KnownState] = &[Arizona, California, NewYork];
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
    fn variant_name(&self) -> &'static str {
        match *self {
            Arizona => "Arizona",
            California => "California",
            NewYork => "NewYork",
            _ => unimplemented!()
        }
    }
    fn check_missing(self, target: &IdMap<KnownState, &'static str>) {
        assert_eq!(target.get(self), None, "Expected no city for {:?}", self);
    }
    fn check_city(self, target: &IdMap<KnownState, &'static str>) {
        assert_eq!(target.get(self), Some(&self.city()), "Unexpected city for {:?}", self);
    }
}

#[test]
fn test_wrapper() {
    let data = idmap! {
        ExampleWrapper(32) => "abc",
        ExampleWrapper(42) => "life"
    };
    assert_eq!(data[ExampleWrapper(32)], "abc");
    assert_eq!(data[ExampleWrapper(42)], "life");
    assert_eq!(data.get(ExampleWrapper(76)), None)
}

#[test]
fn test_struct_wrapper() {
    let data = idmap! {
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
    let mut expected_tokens = vec![Token::Map { len: Some(3) }];
    for state in IMPORTANT_STATES {
        expected_tokens.extend(&[
            Token::Enum { name: "KnownState" },
            Token::Str(state.variant_name()),
            Token::Unit,
            Token::BorrowedStr(state.city())
        ]);
    }
    expected_tokens.push(Token::MapEnd);
    assert_tokens(&important_cities(), &expected_tokens);
}

