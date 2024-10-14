#[cfg(feature = "std")]
extern crate std;
#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(feature = "std")]
pub use std::{vec::Vec, borrow::Cow, string::String, error::Error};
#[cfg(not(feature = "std"))]
pub use alloc::{vec::Vec, borrow::Cow, string::String};

#[cfg(all(not(feature = "std"), feature = "error_in_core"))]
pub use core::error::Error;

pub trait VecExt<T> {
    fn first_mut_or_push(&mut self, value: T) -> &mut T;
}

impl<T> VecExt<T> for Vec<T> {
    fn first_mut_or_push(&mut self, value: T) -> &mut T {
        if self.is_empty() { self.push(value); }
        self.first_mut()
            .expect("there must be at least one element here due to the push above")
    }
}