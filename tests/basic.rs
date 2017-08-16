#[macro_use]
extern crate idmap;
#[macro_use]
extern crate idmap_derive;

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
#[derive(IntegerId, Debug, Copy, Clone, PartialEq)]
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

#[derive(IntegerId, Debug, PartialEq)]
struct ExampleWrapper(u16);
