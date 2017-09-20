use std::rc::Rc;
use std::sync::Arc;
use std::convert::TryFrom;
use std::fmt::{Debug, Display};

use core::nonzero::{NonZero, Zeroable};

/// A type that can be uniquely identified by a 64 bit integer id
pub trait IntegerId: PartialEq + Debug {
    type Storage;
    fn from_storage(storage: Self::Storage, id: u64) -> Self;
    fn into_storage(self) -> Self::Storage;
    /// Return the unique id of this value.
    /// If two values are equal, they _must_ have the same id,
    /// and if two values aren't equal, they _must_ have different ids.
    fn id(&self) -> u64;
    /// Return the 32-bit unique id of this value, panicking on overflow
    fn id32(&self) -> u32;
}
#[cfg(feature = "nonzero")] // Hidden behind a (default) feature flag for docs.rs
impl<T: IntegerId + Zeroable + Copy> IntegerId for NonZero<T> {
    type Storage = T::Storage;
    #[inline]
    fn from_storage(storage: T::Storage, id: u64) -> Self {
        let value = T::from_storage(storage, id);
        NonZero::new(value).unwrap()
    }
    #[inline]
    fn into_storage(self) -> T::Storage {
        self.get().into_storage()
    }
    #[inline]
    fn id(&self) -> u64 {
        self.get().id()
    }
    #[inline]
    fn id32(&self) -> u32 {
        self.get().id32()
    }
}
macro_rules! primitive_id {
    ($target:ty, fits32 = false, signed = true) => {
        impl IntegerId for $target {
            type Storage = ();
            #[inline(always)]
            fn from_storage(_: (), id: u64) -> Self {
                id as $target
            }
            #[inline(always)]
            fn into_storage(self) {}
            #[inline(always)]
            #[cfg_attr(feature = "cargo-clippy", allow(cast_lossless))]
            fn id(&self) -> u64 {
                *self as u64
            }
            #[inline]
            fn id32(&self) -> u32 {
                /* 
                 * NOTE: We attempt the lossy conversion to i32 for signed ints, then convert to u32 afterwords.
                 * If we casted directly from i64 -> u32 it'd fail for negatives,
                 * and if we casted from i64 -> u64 first, small negatives would fail to cast since they'd be too large.
                 * For example, -1 would become 0xFFFFFFFF which would overflow a u32,
                 * but if we first cast to a i32 it'd become 0xFFFF which would fit fine.                         
                 */
                let full_value = *self;
                if let Ok(value) = i32::try_from(full_value) {
                    value as u32
                } else {
                    id_overflowed(full_value)
                }
            }
        }
    };
    ($target:ty, fits32 = false, signed = false) => {
        impl IntegerId for $target {
            type Storage = ();
            #[inline(always)]
            fn from_storage(_: (), id: u64) -> Self {
                id as $target
            }
            #[inline(always)]
            fn into_storage(self) {}
            #[inline(always)]
            #[cfg_attr(feature = "cargo-clippy", allow(cast_lossless))]
            fn id(&self) -> u64 {
                *self as u64
            }
            #[inline]
            fn id32(&self) -> u32 {
                let full_value = *self;
                if let Ok(value) = u32::try_from(full_value) {
                    value
                } else {
                    id_overflowed(full_value)
                }
            }
        }
    };
    ($target:ty, fits32 = true) => {
        impl IntegerId for $target {
            type Storage = ();
            #[inline(always)]
            fn from_storage(_: (), id: u64) -> Self {
                // TODO: Should we have a debug_assert! to check the cast?
                id as $target
            }
            #[inline(always)]
            fn into_storage(self) {}
            #[inline(always)]
            #[cfg_attr(feature = "cargo-clippy", allow(cast_lossless))]
            fn id(&self) -> u64 {
                *self as u64
            }
            #[inline(always)]
            #[cfg_attr(feature = "cargo-clippy", allow(cast_lossless))]
            fn id32(&self) -> u32 {
                *self as u32
            }
        }
    };
}

/// Support function that panics if an id overflows a u32
#[cfg_attr(feature="cargo-clippy", allow(needless_pass_by_value))] // It's more efficient
#[cold] #[inline(never)]
fn id_overflowed<T: Display>(id: T) -> ! {
    panic!("ID overflowed a u32: {}", id);
}
primitive_id!(u64, fits32 = false, signed = false);
primitive_id!(i64, fits32 = false, signed = true);
primitive_id!(usize, fits32 = false, signed = false);
primitive_id!(isize, fits32 = false, signed = true);
primitive_id!(u32, fits32 = true);
primitive_id!(i32, fits32 = true);
primitive_id!(u16, fits32 = true);
primitive_id!(i16, fits32 = true);
macro_rules! generic_deref_id {
    ($target:tt) => {
        impl<T: IntegerId> IntegerId for $target<T> {
            type Storage = Self;
            #[inline(always)]
            fn from_storage(storage: Self, _: u64) -> Self {
                storage
            }
            #[inline(always)]
            fn into_storage(self) -> Self {
                self
            }
            #[inline]
            fn id(&self) -> u64 {
                (**self).id()
            }

            #[inline]
            fn id32(&self) -> u32 {
                (**self).id32()
            }
        }
    };
}
generic_deref_id!(Rc);
generic_deref_id!(Box);
generic_deref_id!(Arc);
