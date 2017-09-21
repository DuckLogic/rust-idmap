rust-idmap [![Crates.io](https://img.shields.io/crates/v/idmap.svg)](https://crates.io/crates/idmap) [![Documentation](https://docs.rs/idmap/badge.svg)](https://docs.rs/idmap)
==========
Efficient maps of integer id keys to values, backed by an underlying `Vec`.

## Features
- Automiatically derived `IntegerId` for enums and newtype structs
  - Implemented in the `idmap-derive` proc_macro crate
- Maintains insertion order of the entries, as there's an indirection like `OrderMap`.
  - Therefore, entries which aren't present take little space, as only a `u32` needs to be stored.
  - This indirection can be avoided with a `DirectIdMap` which doesn't preserve order,
    and saves space when the ids of the map's keys are densly packed and mostly present.
