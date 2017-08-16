rust-idmap
==========
Efficient maps of integer id keys to values, backed by an underlying `Vec`.

## Features
- Automiatically derived `IntegerId` for enums and newtype structs
  - Implemented in the `idmap-derive` proc_macro crate
- Maintains insertion order of the entries, as there's an iderection like `OrderMap`.
  - Therefore, entries which aren't present take little space, as only a `u32` needs to be stored.
- Supports a `CompactIdMap` which handles indexes offset from the start element.

