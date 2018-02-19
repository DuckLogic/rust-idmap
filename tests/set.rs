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

use idmap::IdSet;
use KnownState::*;

#[test]
fn test_remove() {
    let mut m = important_states();
    assert_eq!(m.remove(NewMexico), false);
    for state in IMPORTANT_STATES {
        assert_eq!(m.remove(state), true);
    }
    assert_eq!(m.len(), 0);
    assert_eq!(m.remove(NewMexico), false);
    assert_eq!(m.remove(NorthDakota), false);
}

#[test]
fn test_eq() {
    let first = important_states();
    let mut second = important_states().iter().collect_vec();
    second.reverse();
    let second = second.iter().collect::<IdSet<_>>();

    assert_eq!(first, second);
}

#[test]
fn test_from_iter() {
    let xs = [California, NewYork, Arizona];

    let set: IdSet<_> = xs.iter().cloned().collect();

    for state in &xs {
        assert_eq!(set[state], true);
    }
    check_missing(TINY_STATES, &set);
}

#[test]
fn test_clone() {
    let original = important_states();
    let cloned = original.clone();
    assert_eq!(original, cloned);
}

#[test]
fn test_index() {
    let set = important_states();

    for state in IMPORTANT_STATES {
        assert_eq!(set[state], true);
    }
    assert_eq!(set[NorthDakota], false);
}

#[test]
fn test_entry_insert() {
    let mut set = important_states();

    for &state in ALL_STATES {
        set.insert(state);
    }
    check_cities(ALL_STATES, &set);
}

#[test]
fn test_extend_ref() {
    let important = important_states();
    let mut all = IdSet::new();
    all.insert(NewMexico);
    all.insert(California);
    all.insert(NorthDakota);

    all.extend(&important);

    assert_eq!(all.len(), 5);
    // Updates must remain in declaration order
    assert_eq!(all.iter().nth(1).unwrap(), California);
    assert_eq!(all.iter().nth(4).unwrap(), NorthDakota);
    check_cities(ALL_STATES, &all);
}

/// List the biggest cities in each state except for `NewMexico` and `NorthDakota`,
/// intentionally excluding them to provide a better test case.
fn important_states() -> IdSet<KnownState> {
    idset!(Arizona, NewYork, California)
}
#[derive(IntegerId, Debug, Copy, Clone, PartialEq, Serialize, Deserialize, Ord, PartialOrd, Eq)]
enum KnownState {
    Arizona,
    California,
    NewMexico,
    NewYork,
    NorthDakota
}
fn check_missing(states: &[KnownState], target: &IdSet<KnownState>) {
    for state in states {
        assert_eq!(target[state], false);
    }
}
fn check_cities(states: &[KnownState], target: &IdSet<KnownState>) {
    for state in states {
        assert_eq!(target[state], true);
    }
}
static ALL_STATES: &[KnownState] = &[Arizona, California, NewMexico, NewYork, NorthDakota];
// NOTE: Intentionally out of declared order to try and mess things up

static IMPORTANT_STATES: &[KnownState] = &[Arizona, NewYork, California];
static TINY_STATES: &[KnownState] = &[NorthDakota, NewMexico];

#[test]
fn test_wrapper() {
    let data = idset!(ExampleWrapper(32), ExampleWrapper(42));
    assert_eq!(data[ExampleWrapper(32)], true);
    assert_eq!(data[ExampleWrapper(42)], true);
    assert_eq!(data[ExampleWrapper(76)], false);
}

#[test]
fn test_struct_wrapper() {
    let data = idset!(ExampleStructWrapper::new(32), ExampleStructWrapper::new(42));
    assert_eq!(data[ExampleStructWrapper::new(32)], true);
    assert_eq!(data[ExampleStructWrapper::new(42)], true);
    assert_eq!(data[ExampleStructWrapper::new(76)], false)
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
        ($len:expr, $($state:ident),*) => (&[
            Token::Seq { len: Some($len) },
            $(
                Token::Enum { name: "KnownState" },
                Token::Str(stringify!($state)),
                Token::Unit,
            )*
            Token::SeqEnd
        ]);
    }
    // Remember, IdSet serializes in _declaration order_
    const EXPECTED_TOKENS: &[Token] = state_tokens!(3,
        Arizona,
        California,
        NewYork
    );
    assert_tokens(&important_states(), EXPECTED_TOKENS);
}

