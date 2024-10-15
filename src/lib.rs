#![doc = include_str!("../README.md")]
#![warn(missing_docs)]
#![forbid(unsafe_code)]
#![no_std]
#![cfg_attr(feature = "f16", feature(f16))]

#[cfg(not(any(feature = "std", feature = "libm")))]
compile_error!("either libm or the standard library must be included to use omeganum");



use core::{cmp::Ordering, fmt, ops::*, str::FromStr};


/// Re-export of [`num_traits`] for convenience.
pub use num_traits;
use num_traits::{ConstOne, ConstZero, Float, Num, One, Signed, ToPrimitive, Zero};

mod shims;
use shims::*;

mod constants;
use constants::*;

#[doc(hidden)]
pub use constants::{EMPTY_ARRAY, MAX_SAFE_INTEGER_F, MIN_SAFE_INTEGER_F};

mod parsing;
pub use parsing::FromStrError;

#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
#[derive(Debug, Clone, PartialEq)] // The PartialEq implementation is correct
/// A number that stores values up to `10{N}M` for some integer N and float M.
pub struct OmegaNum {
    base: f64,
    array: Cow<'static, [f64]>,
}

#[macro_export]
/// Create a statically-known [`OmegaNum`].
///
/// You should use this when you need a constant value of specifically type [`OmegaNum`].
/// If the context you're using this in doesn't demand that, it's likely more clear to coerce from a primitive.
/// 
/// # Errors
/// Will cause a compiler error if the given value would require an allocation.
///
/// The exact range for values not requiring an allocation is
/// - Non-finite values (i.e. [`f64::INFINITY`], [`f64::NEG_INFINITY`], and [`f64::NAN`]),
/// - Values with an absolute value &leq; 2<sup>53</sup>-1.
///
/// Unfortunately, constant evaluation is not strong enough as of writing
/// to support values outside of this range. If you need a constant outside of this range,
/// the easiest way is to create a small program that constructs it
/// and then prints its parts from [`OmegaNum::into_parts`], and passing that to [`OmegaNum::from_parts`] (which is `const`).
macro_rules! constant {
    ($expr: expr) => {{
        const NUM: f64 = { $expr } as f64;
        const {
            assert!(
                !(!(
                    NUM < f64::MIN ||
                    NUM > f64::MAX ||
                    NUM != NUM
                ) && (NUM < $crate::MIN_SAFE_INTEGER_F || NUM > $crate::MAX_SAFE_INTEGER_F)),
                "constant omeganum value outside of supported range (non-finite, or 2^53-1 on both ends)"
            );
            $crate::OmegaNum::from_parts(NUM, $crate::EMPTY_ARRAY)
        }
    }};
}

impl ToPrimitive for OmegaNum {
    fn to_f64(&self) -> Option<f64> {
        Some(self.to_f64())
    }

    fn to_i64(&self) -> Option<i64> {
        self.to_f64().to_i64()
    }

    fn to_u64(&self) -> Option<u64> {
        if self.is_negative() {
            return None;
        }
        self.to_i64().map(|v| v as u64)
    }
}

impl From<f64> for OmegaNum {
    #[inline]
    fn from(first: f64) -> Self {
        Self {
            base: first,
            array: EMPTY_ARRAY,
        }
        .normalized()
    }
}

impl From<OmegaNum> for f64 {
    #[inline]
    fn from(from: OmegaNum) -> Self {
        from.to_f64()
    }
}

impl Zero for OmegaNum {
    #[inline]
    fn zero() -> Self {
        Self::ZERO
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.base.is_zero()
    }

    fn set_zero(&mut self) {
        self.array.to_mut().clear();
        self.base = 0.0;
    }
}

impl ConstZero for OmegaNum {
    const ZERO: Self = constant!(0.0);
}

impl One for OmegaNum {
    #[inline]
    fn one() -> Self {
        Self::ONE
    }

    fn set_one(&mut self) {
        self.array.to_mut().clear();
        self.base = 1.0;
    }
}

impl ConstOne for OmegaNum {
    const ONE: Self = constant!(1.0);
}

impl Signed for OmegaNum {
    #[inline]
    fn abs(&self) -> Self {
        Self {
            base: self.base.abs(),
            array: self.array.clone(),
        }
    }

    #[inline]
    fn abs_sub(&self, other: &Self) -> Self {
        if self <= other {
            return Self::ZERO;
        }
        self.clone() - other.clone()
    }

    #[inline]
    fn signum(&self) -> Self {
        Self {
            base: self.base.signum(),
            array: EMPTY_ARRAY,
        }
    }

    #[inline]
    fn is_positive(&self) -> bool {
        self.is_positive()
    }

    #[inline]
    fn is_negative(&self) -> bool {
        self.is_negative()
    }
}

macro_rules! forward_from {
    ($($(@$From: ident)? $ty: ty),*) => {$(
        $(impl $From<$ty> for OmegaNum {
            fn from(val: $ty) -> OmegaNum {
                Self::from(val as f64)
            }
        })?

        impl PartialEq<$ty> for OmegaNum {
            fn eq(&self, other: &$ty) -> bool {
                self.eq(&(Self::from(*other)))
            }
        }

        impl PartialEq<OmegaNum> for $ty {
            fn eq(&self, other: &OmegaNum) -> bool {
                OmegaNum::from(*self).eq(other)
            }
        }
        
        impl PartialOrd<$ty> for OmegaNum {
            fn partial_cmp(&self, other: &$ty) -> Option<Ordering> {
                self.partial_cmp(&(Self::from(*other)))
            }
        }

        impl PartialOrd<OmegaNum> for $ty {
            fn partial_cmp(&self, other: &OmegaNum) -> Option<Ordering> {
                OmegaNum::from(*self).partial_cmp(other)
            }
        }
    )*}
}

forward_from! {
    f64, @From f32, 
    @From i8, @From i16, @From i32, @From i64, @From i128, 
    @From u8, @From u16, @From u32, @From u64, @From u128
}
#[cfg(feature = "f16")]
forward_from! { @From f16 }

impl PartialOrd for OmegaNum {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.base.is_nan() || other.base.is_nan() {
            return None;
        }
        let Self { base, array } = other;

        if self.base.is_infinite() {
            let res = self.base.partial_cmp(base);
            if res != Some(Ordering::Equal) {
                return res;
            } // This handles NaN, Infinity, etc.
        }

        if other.base.is_infinite() {
            return Some(if other.base.is_sign_negative() {
                Ordering::Greater
            } else {
                Ordering::Less
            });
        }

        match self.base.signum().partial_cmp(&other.base.signum()) {
            Some(Ordering::Equal) => {},
            other => return other
        }

        if self.array.len() != array.len() {
            let mut res = self.array.len().cmp(&array.len());
            if self.base.is_sign_negative() {
                res = res.reverse();
            }
            return Some(res);
        }
        if self.array.is_empty() {
            return self.base.partial_cmp(&other.base);
        }

        let mut res = Ordering::Equal;
        for (lhs, rhs) in self.array.iter().rev().zip(array.iter().rev()) {
            match lhs.partial_cmp(rhs)? {
                Ordering::Equal => {}
                other => {
                    res = other;
                    break;
                }
            }
        }
        if res == Ordering::Equal {
            match self.base.partial_cmp(base)? {
                Ordering::Equal => {}
                other => return Some(other),
            }
        }
        if self.base.is_sign_negative() {
            res = res.reverse()
        }
        Some(res)
    }
}

impl Neg for OmegaNum {
    type Output = OmegaNum;

    fn neg(self) -> Self::Output {
        OmegaNum {
            base: -self.base,
            array: self.array,
        }
    }
}

impl AddAssign for OmegaNum {
    fn add_assign(&mut self, other: Self) {
        if self.is_nan() {
            return;
        }
        if other.is_nan()
            || (self.is_infinite()
                && other.is_infinite()
                && (self.is_negative() ^ other.is_negative()))
        {
            *self = Self::NAN;
            return;
        }
        if other == Self::ZERO {
            return;
        }
        if *self == Self::ZERO {
            *self = other;
            return;
        }
        if self.is_negative() {
            self.negate();
            *self -= other;
            self.negate();
            return;
        }
        if other.is_negative() {
            *self -= -other;
            return;
        }
        if self.is_infinite() || other.is_infinite() {
            return;
        }
        let min = self.min(&other);
        let max = self.max(&other);
        if max.array.is_empty() {
            self.base += other.base;
            self.array.to_mut().clear();
            self.normalize();
        } else if *max > E_MAX_SAFE_INTEGER
            // Using properties of logarithms, we avoid division which would make this recursive
            || !(max.clone().log10() - min.clone().log10()).exp10().array.is_empty()
        {
            *self = max.clone();
        } else if max.array[0] == 1.0 {
            let diff = if min.array.is_empty() {
                min.base.log10()
            } else {
                min.base
            };
            *self = Self {
                base: diff + (10.0.powf(max.base - diff) + 1.0).log10(),
                array: Cow::Borrowed(&[1.0]),
            }
            .normalized()
        } else {
            // This only happens if one of the arguments isn't normalized
            self.normalize();
            *self += other.normalized();
        }
    }
}

impl SubAssign for OmegaNum {
    fn sub_assign(&mut self, other: Self) {
        if self.is_nan() {
            return;
        }
        if other.is_nan() {
            *self = Self::NAN;
            return;
        }
        if self.is_infinite() {
            if other.is_infinite() && self.is_negative() == other.is_negative() {
                *self = Self::NAN;
            }
            return;
        }
        if other.is_infinite() {
            *self = -other;
            return;
        }
        if other == Self::ZERO {
            return;
        }
        if *self == Self::ZERO {
            *self = -other;
            return;
        }
        if *self == other {
            *self = Self::ZERO;
            return;
        }
        if other.is_negative() {
            *self += -other;
            return;
        }
        if self.is_negative() {
            self.negate();
            *self += other;
            self.negate();
            return;
        }

        let min = self.min(&other);
        let max = self.max(&other);
        if max.array.is_empty() {
            self.array.to_mut().clear();
            self.base -= other.base;
            self.normalize();
            return;
        }
        let other_gt_self = *self < other;
        let max_l10 = max.clone().log10();
        let min_l10 = min.clone().log10();
        if *max > E_MAX_SAFE_INTEGER || !(max_l10 - min_l10).exp10().array.is_empty() {
            *self = max.clone();
        } else if max.array[0] == 1.0 {
            let diff = if min.array.is_empty() {
                min.base.log10()
            } else {
                min.base
            };
            *self = OmegaNum {
                base: diff + (10.0.powf(self.base - diff) - 1.0).log10(),
                array: Cow::Borrowed(&[1.0]),
            }
        } else {
            // This only happens if one of the arguments isn't normalized
            self.normalize();
            *self -= other.normalized();
        }
        if other_gt_self {
            self.negate();
        }
    }
}

impl MulAssign for OmegaNum {
    fn mul_assign(&mut self, other: Self) {
        if self.is_nan() {
            return;
        }
        if self.is_negative() ^ other.is_negative() {
            self.absolutize();
            *self *= other.abs();
            self.negate();
            return;
        }
        if self.is_negative() {
            self.absolutize();
            *self *= other.abs();
            return;
        }
        if other.is_nan()
            || *self == Self::ZERO && other.is_infinite()
            || self.is_infinite() && other == Self::ZERO
        {
            *self = Self::NAN;
            return;
        }
        if *self == Self::ZERO || other == Self::ZERO {
            // Keep track of -0
            let base_sign = self.base * other.base;
            *self = Self::ZERO;
            self.base = self.base.copysign(base_sign);
            return;
        }
        if other == Self::ONE {
            return;
        }
        if self.is_infinite() {
            return;
        }
        if other.is_infinite() {
            *self = other;
            return;
        }
        if *self.max(&other) > EE_MAX_SAFE_INTEGER {
            if other > *self {
                *self = other;
            }
            return;
        }
        let mul = self.to_f64() * other.to_f64();
        if mul <= MAX_SAFE_INTEGER_F {
            *self = OmegaNum::from(mul);
        } else {
            *self = (self.clone().log10() + other.log10()).exp10();
        }
    }
}

impl DivAssign for OmegaNum {
    fn div_assign(&mut self, other: Self) {
        if self.is_nan() {
            return;
        }
        if self.is_negative() ^ other.is_negative() {
            self.absolutize();
            *self /= other.abs();
            self.negate();
            return;
        }
        if self.is_negative() {
            self.absolutize();
            *self /= other.abs();
            return;
        }
        if other.is_nan()
            || self.is_infinite() && other.is_infinite()
            || *self == Self::ZERO && other == Self::ZERO
        {
            *self = Self::NAN;
            return;
        }
        if other == Self::ZERO {
            *self = Self::INFINITY;
            return;
        }
        if other == Self::ONE {
            return;
        }
        if *self == other {
            *self = Self::ONE;
            return;
        }
        if self.is_infinite() {
            return;
        }
        if other.is_infinite() {
            *self = Self::ZERO;
            return;
        }
        if *self.max(&other) > EE_MAX_SAFE_INTEGER {
            if *self < other {
                *self = Self::ZERO;
            }
            return;
        }
        let div = self.to_f64() / other.to_f64();
        if div <= MAX_SAFE_INTEGER_F {
            *self = OmegaNum::from(div);
            return;
        }
        *self = (self.clone().log10() - other.log10()).exp10();
    }
}

impl RemAssign for OmegaNum {
    fn rem_assign(&mut self, other: Self) {
        if self.is_nan() || other.is_nan() {
            *self = Self::NAN;
            return;
        }
        if other == Self::ZERO {
            *self = Self::ZERO;
            return;
        }
        if self.is_negative() ^ other.is_negative() {
            self.absolutize();
            *self %= other.abs();
            self.negate();
            return;
        }
        if self.is_negative() {
            self.absolutize();
            *self %= other.abs();
            return;
        }
        let mut nearest_mul = self.clone();
        nearest_mul /= other.clone();
        nearest_mul = nearest_mul.floor();
        nearest_mul *= other;
        *self -= nearest_mul;
    }
}


macro_rules! forward_binop_impl {
    (
        $($impl_assign_name: ident: $assign_name: ident, $impl_name: ident: $name: ident;)+
        ($($($ty: ty),+)+)
    ) => {$(
        impl $impl_name for OmegaNum {
            type Output = OmegaNum;

            fn $name(mut self, rhs: Self) -> Self {
                self.$assign_name(rhs);
                self
            }
        }

        forward_binop_impl! {
            @impls $impl_assign_name: $assign_name, $impl_name: $name;
            $($ty)*
        }
    )*};

    (
        @impls $impl_assign_name: ident: $assign_name: ident, $impl_name: ident: $name: ident;
        $($ty: ty)+
    ) => {$(
        impl $impl_name<$ty> for OmegaNum {
            type Output = OmegaNum;

            fn $name(self, rhs: $ty) -> Self {
                <Self as $impl_name>::$name(self, Self::from(rhs))
            }
        }

        impl $impl_name<OmegaNum> for $ty {
            type Output = OmegaNum;

            fn $name(self, rhs: OmegaNum) -> OmegaNum {
                <OmegaNum as $impl_name>::$name(OmegaNum::from(self), rhs)
            }
        }

        impl $impl_assign_name<$ty> for OmegaNum {
            fn $assign_name(&mut self, rhs: $ty) {
                self.$assign_name(Self::from(rhs))
            }
        }
    )*}
}

forward_binop_impl! {
    AddAssign: add_assign, Add: add;
    SubAssign: sub_assign, Sub: sub;
    MulAssign: mul_assign, Mul: mul;
    DivAssign: div_assign, Div: div;
    RemAssign: rem_assign, Rem: rem;
    (
        f64, f32, u8, u16, u32, u64, u128, i8, i16, i32, i64, i128
        f64, f32, u8, u16, u32, u64, u128, i8, i16, i32, i64, i128
        f64, f32, u8, u16, u32, u64, u128, i8, i16, i32, i64, i128
        f64, f32, u8, u16, u32, u64, u128, i8, i16, i32, i64, i128
        f64, f32, u8, u16, u32, u64, u128, i8, i16, i32, i64, i128
    )
}
#[cfg(feature = "f16")]
forward_binop_impl! { @impls AddAssign: add_assign, Add: add; f16 }
#[cfg(feature = "f16")]
forward_binop_impl! { @impls SubAssign: sub_assign, Sub: sub; f16 }
#[cfg(feature = "f16")]
forward_binop_impl! { @impls MulAssign: mul_assign, Mul: mul; f16 }
#[cfg(feature = "f16")]
forward_binop_impl! { @impls DivAssign: div_assign, Div: div; f16 }
#[cfg(feature = "f16")]
forward_binop_impl! { @impls RemAssign: rem_assign, Rem: rem; f16 }


impl OmegaNum {
    /// Euler's constant.
    pub const E: Self = constant!(core::f64::consts::E);
    /// Not a number, as defined in IEEE754.
    pub const NAN: Self = constant!(f64::NAN);
    /// A positive infintite value.
    pub const INFINITY: Self = constant!(f64::INFINITY);
    /// A negative infinite value.
    pub const NEG_INFINITY: Self = constant!(f64::NEG_INFINITY);
    /// A negative value that is small enough to be equivalent to 0 as per IEEE754.
    pub const NEG_ZERO: Self = constant!(-0.0);

    #[inline]
    /// Normalizes a number, turning it into its canonical representation.
    pub fn normalized(mut self) -> Self {
        self.normalize();
        self
    }

    /// Normalizes a number in place, turning it into its canonical representation.
    pub fn normalize(&mut self) {
        if !self.base.is_finite() {
            self.array.to_mut().clear();
            return;
        }
        while self.array.last().is_some_and(|last| *last == 0.0) {
            self.array.to_mut().pop();
        }
        let mut keep_going = true;
        while keep_going {
            keep_going = false;
            if self.base > MAX_SAFE_INTEGER_F {
                *self.array.to_mut().first_mut_or_push(0.0) += 1.0;
                self.base = self.base.log10();
                keep_going = true;
            }
            while self.base < MAX_E && self.array.first().is_some_and(|f| *f > 0.0) {
                self.base = 10.0.powf(self.base);
                *self
                    .array
                    .to_mut()
                    .first_mut()
                    .expect("checked that first existed in while loop") -= 1.0;
                keep_going = true;
            }
            let mut i = 0;
            while i < self.array.len() {
                if self.array[i] > MAX_SAFE_INTEGER_F {
                    if i + 1 == self.array.len() {
                        self.array.to_mut().push(0.0);
                    }
                    self.array.to_mut()[i + 1] += 1.0;
                    let new_base = self.array[i] + 1.0;
                    self.array.to_mut()[0..=i].fill(0.0);
                    if new_base > MAX_SAFE_INTEGER_F {
                        self.base = new_base.log10();
                        self.array.to_mut()[0] += 1.0;
                    } else {
                        self.base = new_base;
                    }
                    keep_going = true;
                }
                i += 1;
            }
        }
    }

    #[inline]
    /// Returns how much space this number is taking up on the heap.
    pub fn heap_size(&self) -> usize {
        self.array.len() * core::mem::size_of::<f64>()
    }

    #[inline]
    /// Reduces a number into a base and array.
    pub fn into_parts(self) -> (f64, Cow<'static, [f64]>) {
        (self.base, self.array)
    }

    #[inline]
    /// Constructs an OmegaNum from a base and array.
    ///
    /// # Note
    /// If not already normalized, you _must_ call `OmegaNum::normalize` on the return value of this function.
    /// 
    /// Failure to call this will cause incorrect (although not undefined) behavior.
    pub const fn from_parts(base: f64, array: Cow<'static, [f64]>) -> Self {
        Self { base, array }
    }

    #[inline]
    /// Takes the absolute value of this number in-place.
    pub fn absolutize(&mut self) {
        self.base = self.base.abs();
    }

    #[inline]
    /// Takes the negation of this number in-place.
    pub fn negate(&mut self) {
        self.base = -self.base;
    }

    /// Converts this number to an [`f64`] without consuming it.
    pub fn to_f64(&self) -> f64 {
        if self.array.is_empty() || !self.base.is_finite() {
            return self.base;
        }
        if self.base < 0. {
            return -self.abs().to_f64();
        }
        if self.array.len() > 1 {
            return f64::INFINITY;
        }
        10f64.powf(self.base)
    }

    #[inline]
    /// Tests whether this is NaN.
    pub fn is_nan(&self) -> bool {
        self.base.is_nan()
    }

    #[inline]
    /// Tests whether this has infinite value.
    pub fn is_infinite(&self) -> bool {
        self.base.is_infinite()
    }

    #[inline]
    /// Tests whether this is neither NaN nor infinite.
    pub fn is_finite(&self) -> bool {
        self.base.is_finite()
    }

    #[inline]
    /// Returns whether this number's array is empty - 
    /// that is, whether the value can be stored in an [`f64`] without loss of precision.
    pub fn is_simple(&self) -> bool {
        self.array.is_empty()
    }

    #[inline]
    /// Returns whether this number is an integer.
    pub fn is_integer(&self) -> bool {
        self.is_finite() && (!self.array.is_empty() || self.base % 1.0 == 0.0)
    }

    #[inline]
    /// Returns the largest integer &leq; this number. 
    pub fn floor(self) -> Self {
        if self.is_integer() {
            return self;
        }
        Self {
            base: self.base.floor(),
            ..self
        }
    }

    #[inline]
    /// Returns the smallest integer &geq; this number;
    pub fn ceil(self) -> Self {
        if self.is_integer() {
            return self;
        }
        Self {
            base: self.base.ceil(),
            ..self
        }
    }

    #[inline]
    /// Returns the closest integer to this number.
    pub fn round(self) -> Self {
        if self.is_integer() {
            return self;
        }
        Self {
            base: self.base.round(),
            ..self
        }
    }

    #[inline]
    /// Returns this number with the fractional part removed.
    pub fn trunc(self) -> Self {
        if self.is_integer() {
            return self;
        }
        Self {
            base: self.base.trunc(),
            ..self
        }
    }

    #[inline]
    /// Returns this number with the integral part removed.
    pub fn fract(self) -> Self {
        if self.is_integer() {
            return Self::ZERO;
        }
        Self {
            base: self.base.fract(),
            ..self
        }
    }

    #[inline]
    /// Returns whether this number is positive.
    /// 
    /// # Note
    /// This function will return a non-deterministic value for [`Self::NAN`].
    pub fn is_positive(&self) -> bool {
        self.base.is_sign_positive()
    }

    #[inline]
    /// Returns whether this number is negative.
    /// 
    /// # Note
    /// This function will return a non-deterministic value for [`Self::NAN`].
    pub fn is_negative(&self) -> bool {
        self.base.is_sign_negative()
    }

    #[inline]
    /// Returns the reciprocal of this number.
    pub fn recip(self) -> Self {
        if !self.array.is_empty() {
            return Self::ZERO;
        }
        Self {
            base: self.base.recip(),
            array: EMPTY_ARRAY,
        }
    }

    #[inline]
    /// Raises this number to the power of another.
    pub fn pow(self, other: impl Into<Self>) -> Self {
        self.pow_(other.into())
    }

    fn pow_(self, other: Self) -> Self {
        if self.is_nan() || other.is_nan() {
            return Self::NAN;
        }
        if other == Self::ZERO {
            return Self::ONE;
        }
        if other == Self::ONE {
            return self;
        }
        if other < Self::ZERO {
            return self.pow(-other).recip();
        }
        if self < Self::ZERO {
            if other.is_integer() {
                if other.clone() % 2.0 < Self::ONE {
                    return self.abs().pow(other);
                }
                return -self.abs().pow(other);
            } else {
                return Self::NAN;
            }
        }
        if self == Self::ONE {
            return Self::ONE;
        }
        if self == Self::ZERO {
            return Self::ZERO;
        }
        if self == constant!(10.0) {
            return other.exp10();
        }
        if *self.max(&other) > TETRATED_MAX_SAFE_INTEGER {
            return if self > other { self } else { other };
        }
        if other < Self::ONE {
            return self.root(other.recip());
        }
        let float_res = self.to_f64().powf(other.to_f64());
        if float_res <= MAX_SAFE_INTEGER_F {
            return Self::from(float_res);
        }
        (self.log10() * other).exp10()
    }

    #[inline]
    /// Returns the number so that x<sup>2</sup> = this number.
    pub fn sqrt(self) -> Self {
        self.root_(constant!(2.0))
    }

    #[inline]
    /// Returns the number so that x<sup>3</sup> = this number.
    pub fn cbrt(self) -> Self {
        self.root_(constant!(3.0))
    }

    #[inline]
    /// Returns the number so that x<sup>N</sup> = this number for any N.
    pub fn root(self, other: impl Into<Self>) -> Self {
        self.root_(other.into())
    }

    fn root_(self, other: Self) -> Self {
        if other == Self::ONE {
            return self;
        }
        if other < Self::ZERO {
            return self.root_(-other).recip();
        }
        if other < Self::ONE {
            return self.pow_(other.recip());
        }
        if self < Self::ZERO {
            if other.is_integer() && other.clone() % 2.0 == Self::ONE {
                return -((-self).root_(other));
            }
            return Self::NAN;
        }
        if self == Self::ONE {
            return Self::ONE;
        }
        if self == Self::ZERO {
            return Self::ZERO;
        }
        if *self.max(&other) > TETRATED_MAX_SAFE_INTEGER {
            return if self > other { self } else { Self::ZERO };
        }
        (self.log10() / other).exp10()
    }

    #[inline]
    /// Returns Euler's constant raised to the power of this number. 
    pub fn exp(self) -> Self {
        Self::E.pow(self)
    }

    /// Returns 10 raised to the power of this number.
    /// 
    /// All other exponential functions are implemented in terms of this one.
    pub fn exp10(mut self) -> Self {
        if self == Self::NAN {
            return Self::NAN;
        }
        if self.is_negative() {
            return (-self).exp10().recip();
        }
        if !self.is_finite() {
            return self;
        }
        if self.base > LOG10_MAX {
            *self.array.to_mut().first_mut_or_push(0.0) += 1.0;
        } else {
            self.base = 10.0.powf(self.base);
        }
        self.normalized()
    }

    #[inline]
    /// Returns the number so that e<sup>x</sup> = this number, where e is Euler's constant.
    pub fn ln(self) -> Self {
        self.log10() / Self::E.log10()
    }

    #[inline]
    /// Returns the number so that N<sup>x</sup> = this number, for any N.
    pub fn log(self, base: impl Into<Self>) -> Self {
        self.log10() / base.into().log10()
    }

    /// Returns the number so that 10<sup>x</sup> = this number.
    /// 
    /// All other logarithmic functions are implemented in terms of this one.
    pub fn log10(mut self) -> Self {
        if !self.is_finite() {
            if self == Self::NEG_INFINITY {
                return Self::NAN;
            }
            return self;
        }
        
        let ord = self.partial_cmp(&Self::ZERO).unwrap_or(Ordering::Less);
        // Unwrapping a partial comparison that gives back None will lead this to return NaN, which is what is expected.
        match ord {
            Ordering::Less => Self::NAN,
            Ordering::Equal => Self::NEG_INFINITY,
            Ordering::Greater => {
                if self > TETRATED_MAX_SAFE_INTEGER {
                    return self;
                }
                let Some(first) = self.array.to_mut().first_mut() else {
                    return Self {
                        base: self.base.log10(),
                        ..self
                    };
                };
                *first -= 1.0;
                self.normalized()
            }
        }
    }

    #[inline]
    /// Returns a reference to the larger of this value and the given one.
    pub fn max<'result, 'lhs: 'result, 'rhs: 'result>(
        &'lhs self,
        other: &'rhs Self,
    ) -> &'result Self {
        if self > other {
            self
        } else {
            other
        }
    }

    #[inline]
    /// Returns a reference to the smaller of this value and the given one.
    pub fn min<'result, 'lhs: 'result, 'rhs: 'result>(
        &'lhs self,
        other: &'rhs Self,
    ) -> &'result Self {
        if self < other {
            self
        } else {
            other
        }
    }

    #[inline]
    /// Returns the larger of this number and the given one.
    pub fn max_move(self, other: impl Into<Self>) -> Self {
        let other = other.into();
        if self > other {
            self
        } else {
            other
        }
    }

    #[inline]
    /// Returns the smaller of this number and the given one.
    pub fn min_move(self, other: impl Into<Self>) -> Self {
        let other = other.into();
        if self < other {
            self
        } else {
            other
        }
    }

    /// Constructs an [`OmegaNum`] from a base and an arrow count -
    /// that is, `10{arrow_count}base`.
    ///
    /// # Performance warning
    /// Large counts of arrows will cause your number to become enormous.
    ///
    /// **Care *must* be taken with input to prevent resource exhaustion.**
    pub fn from_arrows(base: f64, arrow_count: usize) -> Self {
        if !base.is_finite() || arrow_count == 0 {
            return Self::from(base);
        }
        if base < 0.0 {
            return -Self::from_arrows(10.0.powf(base), arrow_count - 1);
        }
        if base == 0.0 {
            return Self::ONE;
        }
        if base == 1.0 {
            return Self::from(10.0);
        }

        if base < MAX_E && arrow_count == 1 {
            return Self {
                base: 10.0.powf(base),
                array: EMPTY_ARRAY,
            };
        }

        if arrow_count == 1 {
            if base < MAX_SAFE_INTEGER_F {
                return Self {
                    base,
                    array: Cow::Borrowed(&[1.0]),
                };
            }
            return Self {
                base: base.log10(),
                array: Cow::Borrowed(&[2.0]),
            };
        }

        Self {
            base: TEN_BILLION,
            array: core::iter::repeat(8.0)
                .take(arrow_count - 2)
                .chain(core::iter::once(base - 2.0))
                .collect(),
        }
        .normalized()
    }

    /// Evaluates `{N}` between two values - i.e, `self {N} other`.
    /// 
    /// For example, `{2}` would be `self` &uarr;&uarr; `other`, 
    /// or for `other == 4`, <code>self</code><sup><code>self</code><sup><code>self</code><sup><code>self</code></sup></sup></sup>.
    ///
    /// # Performance warning
    /// This is an incredibly expensive operation,
    /// taking `O((arrows - 1)^2 / 2)`[^1] time,
    /// and will cause your number to become enormous.
    ///
    /// **Care *must* be taken with input to prevent resource exhaustion.**    
    ///
    /// # Panics
    /// Panics if `arrows == usize::MAX`.
    ///
    /// [^1]: Untested, best guess by the author.
    #[inline]
    pub fn arrow(self, arrows: usize, other: impl Into<Self>) -> Self {
        self.arrow_(arrows, other.into())
    }
    
    fn arrow_(self, arrows: usize, other: Self) -> Self {
        if self.is_nan() || other.is_nan() {
            return Self::NAN;
        }
        assert_ne!(
            arrows,
            usize::MAX,
            "cannot execute arrow operation using {arrows} arrows"
        );
        match arrows {
            0 => self * other,
            1 => self.pow(other),
            arrows => {
                if other < Self::ZERO {
                    return Self::NAN;
                }
                if other == Self::ZERO {
                    return Self::ONE;
                }
                if other == Self::ONE {
                    return self;
                }
                if other == constant!(2.0) {
                    return self.clone().arrow(arrows - 1, self);
                }
                if self.max(&other).clone() > OmegaNum::from_arrows(MAX_SAFE_INTEGER_F, arrows + 1)
                {
                    return self.max(&other).clone();
                }
                let max_arrows = OmegaNum::from_arrows(MAX_SAFE_INTEGER_F, arrows);

                let self_gt_max_arrows = self > max_arrows.clone();
                if self_gt_max_arrows || !other.array.is_empty() {
                    let mut ret;
                    if self_gt_max_arrows {
                        ret = self.clone();
                        ret.array.to_mut()[arrows] -= 1.0;
                        ret.normalize();
                    } else if self > OmegaNum::from_arrows(MAX_SAFE_INTEGER_F, arrows - 1) {
                        ret = OmegaNum::from(self.array[arrows - 1]);
                    } else {
                        ret = Self::ZERO;
                    }
                    let mut sum = ret + other;
                    let len = sum.array.len();
                    if len < arrows {
                        sum.array
                            .to_mut()
                            .extend(
                                core::iter::repeat(0.0)
                                .take(arrows - len)
                            );
                    }
                    sum.array.to_mut()[arrows - 1] += 1.0;
                    return sum.normalized();
                }

                let mut factor = other.clone().trunc().to_f64();
                let fract = other.clone().fract();
                let mut ret = self.clone().arrow(arrows - 1, fract);

                let mut force_break = 0;
                while force_break < ARROW_FORCE_BREAK_THRESHOLD
                    && factor > 0.0
                    && ret < OmegaNum::from_arrows(MAX_SAFE_INTEGER_F, arrows - 1)
                {
                    force_break += 1;
                    ret = self.clone().arrow(arrows - 1, ret);
                    factor -= 1.0;
                }
                if force_break == ARROW_FORCE_BREAK_THRESHOLD {
                    factor = 0.0;
                }

                let len = ret.array.len();
                if len < arrows {
                    ret.array
                        .to_mut()
                        .extend(core::iter::repeat(0.0).take(arrows - len - 1));
                }
                ret.array.to_mut()[arrows - 2] += factor;
                ret.normalized()
            }
        }
    }
}

impl fmt::Display for OmegaNum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn write_arrows(f: &mut fmt::Formatter<'_>, arrows: usize) -> fmt::Result {
            if arrows < DISP_MAX_ARROWS {
                for _ in 0..arrows {
                    write!(f, "^")?;
                }
                Ok(())
            } else {
                write!(f, "{{{arrows}}} ")
            }
        }

        if self.array.is_empty() {
            return write!(f, "{}", self.base);
        }
        if self.base < 0.0 {
            write!(f, "-")?;
            return write!(f, "{}", self.abs());
        }
        for (idx, entry) in self.array.iter().enumerate().skip(1).rev() {
            let arrows = idx + 1;
            if *entry == 1.0 {
                write!(f, "10")?;
                write_arrows(f, arrows)?;
                write!(f, " ")?;
            } else if *entry != 0.0 {
                write!(f, "(10")?;
                write_arrows(f, arrows)?;
                write!(f, ")^{entry} ")?;
            }
        }

        if self.array[0] % 1.0 == 0.0 && self.array[0] > 0.0 && self.array[0] < DISP_MAX_E {
            write!(f, "{}{}", "e".repeat(self.array[0] as usize), self.base)
        } else {
            write!(f, "(10^)^{} {}", self.array[0], self.base)
        }
    }
}

impl core::fmt::Display for FromStrError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IncorrectRadix(radix) => {
                write!(f, "can only decode numbers of radix 10 (got {radix})")
            }
            Self::MalformedInput(index) => write!(f, "malformed input at character {index}"),
        }
    }
}

#[cfg(any(feature = "std", feature = "error_in_core", docsrs))]
impl Error for FromStrError {}

impl Num for OmegaNum {
    type FromStrRadixErr = FromStrError;

    fn from_str_radix(string: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        use FromStrError::*;
        if radix != 10 {
            return Err(IncorrectRadix(radix));
        }

        Self::from_str(string)
    }
}

impl FromStr for OmegaNum {
    type Err = FromStrError;

    fn from_str(string: &str) -> Result<Self, Self::Err> {
        let parsed = parsing::parse_omeganum(&mut parsing::ParseHead::new(string)?)?;
        Ok(parsed)
    }
}
