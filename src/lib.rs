#![no_std]
#[cfg(not(any(feature = "std", feature = "libm")))]
compile_error!("either libm or the standard library must be included to use omeganum");

use core::{cmp::Ordering, fmt::{self, Write}, ops::*, str::FromStr};

use num_traits::{ToPrimitive, One, ConstOne, Zero, ConstZero, Signed, Float, Num};

mod shims;
use shims::*;

mod constants;
use constants::*;

mod parsing;
use parsing::FromStrError;

#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
#[derive(Debug, Clone, PartialEq)] // The PartialEq implementation is correct
pub struct OmegaNum {
    base: f64,
    array: Cow<'static, [f64]>
}

#[macro_export]
/// Create a statically-known [`OmegaNum`]. Use whenever possible.
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
/// and then prints its [`fmt::Debug`] representation, passing that to `from_parts`.
macro_rules! constant {
    ($expr: expr) => {{
        const NUM: f64 = { $expr };
        const {
            assert!(
                !(NUM.is_finite() && (NUM < MIN_SAFE_INTEGER_F || NUM > MAX_SAFE_INTEGER_F)),
                "constant omeganum value outside of supported range (non-finite, or 2^53-1 on both ends)"
            );
            Self { base: NUM, array: EMPTY_ARRAY }
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
        if self.is_negative() { return None; }
        self.to_i64().map(|v| v as u64)
    }
}

impl From<f64> for OmegaNum {
    #[inline]
    fn from(first: f64) -> Self {
        Self { base: first, array: EMPTY_ARRAY }.normalized()
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
    fn abs(&self) -> Self {
        Self { base: self.base.abs(), array: self.array.clone() }
    }
    
    fn abs_sub(&self, other: &Self) -> Self {
        if self <= other {
            return Self::ZERO;
        }
        self.clone() - other.clone()
    }
    
    fn signum(&self) -> Self {
        Self { base: self.base.signum(), array: EMPTY_ARRAY }
    }
    
    fn is_positive(&self) -> bool {
        self.is_positive()
    }
    
    fn is_negative(&self) -> bool {
        self.is_negative()
    }
}

impl PartialEq<f64> for OmegaNum {
    fn eq(&self, other: &f64) -> bool {
        self.eq(&(Self::from(*other)))
    }
}

impl PartialOrd<f64> for OmegaNum {
    fn partial_cmp(&self, other: &f64) -> Option<Ordering> {
        self.partial_cmp(&(Self::from(*other)))
    }
}

impl PartialOrd for OmegaNum {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let Self { base, array } = other;
        let res = self.base.partial_cmp(&base);
        if res != Some(Ordering::Equal) { return res } // This handles NaN, Infinity, etc.

        if self.array.len() != array.len() {
            let mut res = self.array.len().cmp(&array.len());
            if self.base.is_sign_negative() { res = res.reverse(); }
            return Some(res)
        }
        if self.array.is_empty() { return Some(Ordering::Equal) }

        let mut res = Ordering::Equal;
        for (lhs, rhs) in self.array.iter().rev()
            .zip(array.iter().rev())
        {
            match lhs.partial_cmp(rhs)? {
                Ordering::Equal => {},
                other => {
                    res = other;
                    break;
                }
            }
        }
        if self.base.is_sign_negative() { res = res.reverse() }
        Some(res)
    }
}

impl Neg for OmegaNum {
    type Output = OmegaNum;

    fn neg(self) -> Self::Output {
        OmegaNum { base: -self.base, array: self.array }
    }
}

macro_rules! forward_binop_impl {
    ($($impl_assign_name: ident: $assign_name: ident, $impl_name: ident: $name: ident);*) => {$(
        impl $impl_name for OmegaNum {
            type Output = OmegaNum;

            fn $name(mut self, rhs: Self) -> Self {
                self.$assign_name(rhs);
                self
            }
        }

        impl $impl_name<f64> for OmegaNum {
            type Output = OmegaNum;

            fn $name(self, rhs: f64) -> Self {
                <Self as $impl_name>::$name(self, Self::from(rhs))
            }
        }

        impl $impl_assign_name<f64> for OmegaNum {
            fn $assign_name(&mut self, rhs: f64) {
                self.$assign_name(Self::from(rhs))
            }
        }
    )*};
}

impl AddAssign for OmegaNum {
    fn add_assign(&mut self, other: Self) {
        if self.is_nan() { return; }
        if other.is_nan() || (
            self.is_infinite() && other.is_infinite() && (self.is_negative() ^ other.is_negative())
        ) {
            *self = Self::NAN;
            return;
        }
        if other == Self::ZERO { return; }
        if *self == Self::ZERO { *self = other; return; }
        if self.is_negative() {
            self.negate();
            *self -= -other;
            self.negate();
            return;
        }
        if other.is_negative() {
            *self -= -other;
            return;
        }
        if self.is_infinite() || other.is_infinite() { return; }
        let min = self.min(&other);
        let max = self.max(&other);
        if max.array.is_empty() {
            self.base += other.base;
            self.array.to_mut().clear();
        } else if *max > E_MAX_SAFE_INTEGER
            || (max.clone() / min.clone()) > MAX_SAFE_INTEGER
        {
            *self = max.clone();
        } else if max.array[0] == 1.0 {
            let diff = if min.array.first().is_some() { min.base } else { min.base.log10() };
            *self = Self {
                base: diff + (10.0.powf(max.base - diff) + 1.0).log10(),
                array: Cow::Borrowed(&[1.0])
            }
        }
    }
}

impl SubAssign for OmegaNum {
    fn sub_assign(&mut self, other: Self) {
        if self.is_nan() { return; }
        if other.is_nan() || (
            self.is_infinite() && other.is_infinite()
        ) {
            *self = Self::NAN;
            return;
        }
        if self.is_infinite() { return; }
        if other.is_infinite() { *self = -other; return; }
        if other == Self::ZERO { return; }
        if *self == Self::ZERO { *self = -other; return; }
        if *self == other { *self = Self::ZERO; return; }
        if other.is_negative() { *self += -other; return; }
        if self.is_negative() { 
            self.negate();
            *self -= -other;
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
        if *max > E_MAX_SAFE_INTEGER
            || (max.clone() / min.clone()) > MAX_SAFE_INTEGER
        {
            *self = max.clone();
        } else if max.array[0] == 1.0 {
            let diff = if min.array.first().is_some() { min.base } else { min.base.log10() };
            *self = OmegaNum {
                base: diff + (10.0.powf(self.base - diff) - 1.0).log10(),
                array: Cow::Borrowed(&[1.0])
            }
        }
        if other_gt_self { self.negate(); }
    }
}

impl MulAssign for OmegaNum {
    fn mul_assign(&mut self, other: Self) {
        if self.is_nan() { return; }
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
            { *self = Self::NAN; return; }
        if *self == Self::ZERO || other == Self::ZERO {
            // Keep track of -0
            let base_sign = self.base * other.base;
            *self = Self::ZERO;
            self.base = self.base.copysign(base_sign);
            return;
        }
        if other == Self::ONE { return; }
        if self.is_infinite() { return; }
        if other.is_infinite() { *self = other; return; }
        if *self.max(&other) > EE_MAX_SAFE_INTEGER {
            if other > *self { *self = other; }
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
        if self.is_nan() { return; }
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
        if other.is_nan() || 
            self.is_infinite() && other.is_infinite() ||
            *self == Self::ZERO && other == Self::ZERO
        {
            *self = Self::NAN;
            return;
        }
        if other == Self::ZERO { *self = Self::INFINITY; return; }
        if other == Self::ONE { return; }
        if *self == other { *self = Self::ONE; return; }
        if self.is_infinite() { return; }
        if other.is_infinite() { *self = Self::ZERO; return; }
        if *self.max(&other) > EE_MAX_SAFE_INTEGER {
            if *self < other { *self = Self::ZERO; }
            return;
        }
        let div = self.to_f64() / other.to_f64();
        if div <= MAX_SAFE_INTEGER_F { *self = OmegaNum::from(div); return; }
        *self = (self.clone().log10() - other.log10()).exp10();
    }
}

impl RemAssign for OmegaNum {
    fn rem_assign(&mut self, other: Self) {
        if other == Self::ZERO { *self = Self::NAN; return; }
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

forward_binop_impl! {
    AddAssign: add_assign, Add: add;
    SubAssign: sub_assign, Sub: sub;
    MulAssign: mul_assign, Mul: mul;
    DivAssign: div_assign, Div: div;
    RemAssign: rem_assign, Rem: rem
}

impl OmegaNum {
    pub const E: Self = constant!(core::f64::consts::E);
    pub const NAN: Self = constant!(f64::NAN);
    pub const INFINITY: Self = constant!(f64::INFINITY);
    pub const NEG_INFINITY: Self = constant!(f64::NEG_INFINITY);
    pub const NEG_ZERO: Self = constant!(-0.0);

    fn normalized(mut self) -> Self {
        self.normalize();
        self
    }

    fn normalize(&mut self) {
        if !self.base.is_finite() {
            self.array.to_mut().clear(); return;
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
            while self.base < MAX_E && self.array.first().is_some_and(|f| *f != 0.0) {
                self.base = self.base.powi(10);
                *self.array.to_mut().first_mut()
                    .expect("checked that first existed in while loop")
                    -= 1.0;
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
                    self.array.to_mut()[0 ..= i].fill(0.0);
                    if new_base > MAX_SAFE_INTEGER_F {
                        self.base = new_base.log10()
                            as f64;
                        self.array.to_mut()[0] += 1.0;
                    } else {
                        self.base = new_base as f64;
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
    pub fn into_parts(self) -> (f64, Cow<'static, [f64]>) {
        (self.base, self.array)
    }

    #[inline]
    /// Constructs an OmegaNum from a base and array.
    /// 
    /// # Note
    /// If not already normalized, you _must_ call `OmegaNum::normalize` on this value.
    /// Failure to call this will cause incorrect (although not undefined) behavior.
    pub const fn from_parts(base: f64, array: Cow<'static, [f64]>) -> Self {
        Self {base, array}
    }

    #[inline]
    pub fn absolutize(&mut self) {
        self.base = self.base.abs();
    }

    #[inline]
    pub fn negate(&mut self) {
        self.base = -self.base;
    }
    
    pub fn to_f64(&self) -> f64 {
        if self.array.is_empty() || !self.base.is_finite() { return self.base }
        if self.base < 0. { return -self.abs().to_f64() }
        if self.array.len() > 1 { return f64::INFINITY }
        return self.base.powi(10);
    }

    #[inline]
    pub const fn is_nan(&self) -> bool {
        self.base.is_nan()
    }

    #[inline]
    pub const fn is_infinite(&self) -> bool {
        self.base.is_infinite()
    }

    #[inline]
    pub const fn is_finite(&self) -> bool {
        self.base.is_finite()
    }

    #[inline]
    pub fn is_normal(&self) -> bool {
        self.array.is_empty() && self.base.is_normal()
    }

    #[inline]
    pub fn is_integer(&self) -> bool {
        !self.array.is_empty()
            || *self >= MAX_SAFE_INTEGER_F
            || self.base % 1.0 == 0.0
    }

    #[inline]
    pub fn floor(self) -> Self {
        if self.is_integer() { return self; }
        Self { base: self.base.floor(), ..self }
    }

    #[inline]
    pub fn ceil(self) -> Self {
        if self.is_integer() { return self; }
        Self { base: self.base.ceil(), ..self }
    }

    #[inline]
    pub fn round(self) -> Self {
        if self.is_integer() { return self; }
        Self { base: self.base.round(), ..self }
    }

    #[inline]
    pub fn trunc(self) -> Self {
        if self.is_integer() { return self; }
        Self { base: self.base.trunc(), ..self }
    }

    #[inline]
    pub fn fract(self) -> Self {
        if self.is_integer() { return Self::ZERO; }
        Self { base: self.base.fract(), ..self }
    }

    #[inline]
    pub fn is_positive(&self) -> bool {
        self.base.is_sign_positive()
    }

    #[inline]
    pub fn is_negative(&self) -> bool {
        self.base.is_sign_negative()
    }

    #[inline]
    pub fn recip(self) -> Self {
        if !self.array.is_empty() { return Self::ZERO; }
        Self { base: self.base.recip(), array: EMPTY_ARRAY }
    }

    pub fn pow(self, other: Self) -> Self {
        if self.is_nan() || other.is_nan() { return Self::NAN; }
        if other == Self::ZERO { return Self::ONE; }
        if other == Self::ONE { return self; }
        if other < Self::ZERO { return self.pow(-other).recip(); }
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
        if self == Self::ONE { return Self::ONE; }
        if self == Self::ZERO { return Self::ZERO; }
        if self == constant!(10.0) { return other.exp10(); }
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
        return (self.log10() * other).exp10()
    }
    
    #[inline]
    pub fn sqrt(self) -> Self {
        self.root(constant!(2.0))
    }

    #[inline]
    pub fn cbrt(self) -> Self {
        self.root(constant!(3.0))
    }

    pub fn root(self, other: Self) -> Self {
        if other == Self::ONE { return self }
        if other < Self::ZERO { return self.root(-other).recip() }
        if other < Self::ONE { return self.pow(other.recip()) }
        if self < Self::ZERO {
            if other.is_integer()
            && other.clone() % 2.0 == Self::ONE
            {
                return -((-self).root(other))
            }
            return Self::NAN;
        }
        if self == Self::ONE { return Self::ONE; }
        if self == Self::ZERO { return Self::ZERO; }
        if *self.max(&other) > TETRATED_MAX_SAFE_INTEGER {
            return if self > other { self } else { Self::ZERO }
        }
        (self.log10() / other).exp10()

    }

    #[inline]
    pub fn exp(self) -> Self {
        Self::E.pow(self)
    }

    pub fn exp10(mut self) -> Self {
        if self == Self::NAN { return Self::NAN; }
        if self.is_negative() {
            return (-self).exp10().recip();
        }
        if !self.is_finite() { return self; }
        if self.base > LOG10_MAX {
            *self.array.to_mut().first_mut_or_push(0.0) += 1.0;
        } else {
            self.base = 10.0.powf(self.base);
        }
        self.normalized()
    }

    #[inline]
    pub fn ln(self) -> Self {
        self.log(Self::E)
    }

    #[inline]
    pub fn log(self, other: Self) -> Self {
        self.log10() / other.log10()
    }

    /// Returns the base 10 logarithm of this number.
    pub fn log10(mut self) -> Self {
        if !self.is_finite() {
            if self == Self::NEG_INFINITY { return Self::NAN; }
            return self;
        }
        // Unwrapping a partial comparison that gives back None will lead this to return NaN, which is what is expected.
        match self.partial_cmp(&Self::ZERO).unwrap_or(Ordering::Less) {
            Ordering::Less => Self::NAN,
            Ordering::Equal => Self::NEG_INFINITY,
            Ordering::Greater => {
                if self > TETRATED_MAX_SAFE_INTEGER {
                    return self;
                }
                let Some(first) = self.array.to_mut().first_mut() else {
                    return Self { base: self.base.log10(), ..self }
                };
                *first -= 1.0;
                return self.normalized();
            }
        }
    }

    #[inline]
    /// Returns the larger of this value and the given one, borrowing both.
    pub fn max<'result, 'lhs: 'result, 'rhs: 'result> (&'lhs self, other: &'rhs Self) -> &'result Self {
        if self > other { self } else { other }
    }

    #[inline]
    /// Returns the smaller of this value and the given one, borrowing both.
    pub fn min<'result, 'lhs: 'result, 'rhs: 'result> (&'lhs self, other: &'rhs Self) -> &'result Self {
        if self < other { self } else { other }
    }

    #[inline]
    /// Returns the larger of this value and the given one, consuming both.
    pub fn max_move(self, other: Self) -> Self {
        if self > other { self } else { other }
    }

    #[inline]
    /// Returns the smaller of this value and the given one, consuming both.
    pub fn min_move(self, other: Self) -> Self {
        if self < other { self } else { other }
    }

    /// Constructs an [`OmegaNum`] from a base and an arrow count - 
    /// that is, `10{arrow_count}base`.
    /// 
    /// # Performance warning
    /// Large counts of arrows will cause your number to become enormous.
    /// 
    /// **Care *must* be taken with input to prevent resource exhaustion.**
    pub fn from_arrows(base: f64, arrow_count: usize) -> Self {
        if !base.is_finite() || arrow_count == 0 { return Self::from(base) }
        if base < 0.0 { 
            return -Self::from_arrows(
                10.0.powf(base),
                arrow_count - 1
            );
        }
        if base == 0.0 { return Self::ONE; }
        if base == 1.0 { return Self::from(10.0); }

        if base < MAX_E && arrow_count == 1 {
            return Self { base: 10.0.powf(base), array: EMPTY_ARRAY };
        }

        if arrow_count == 1 {
            if base < MAX_SAFE_INTEGER_F {
                return Self { base, array: Cow::Borrowed(&[1.0]) };
            }
            return Self { base: base.log10(), array: Cow::Borrowed(&[2.0]) };
        }

        Self {
            base: TEN_BILLION,
            array: core::iter::repeat(8.0)
                .take(arrow_count - 2)
                .chain(core::iter::once(base - 2.0))
                .collect()
        }
    }

    /// Evaluates `{N}` between two values - i.e, `self {N} other`.
    /// For example, `{2}` would be `self ^^ other`, or for `other == 4`, `self ^ self ^ self ^ self`. 
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
    pub fn arrow(self, arrows: usize, other: Self) -> Self {
        if self.is_nan() || other.is_nan() { return Self::NAN; }
        assert_ne!(arrows, usize::MAX, "cannot execute arrow operation using {arrows} arrows");
        match arrows {
            0 => self * other,
            1 => self.pow(other),
            arrows => {
                if other < Self::ZERO { return Self::NAN; }
                if other == Self::ZERO { return Self::ONE; }
                if other == Self::ONE { return self; }
                if other == constant!(2.0) { return self.clone().arrow(arrows - 1, self); }
                if self.max(&other).clone() >
                    OmegaNum::from_arrows(MAX_SAFE_INTEGER_F, arrows + 1)
                {
                    return self.max(&other).clone();
                }
                let max_arrows = OmegaNum::from_arrows(MAX_SAFE_INTEGER_F, arrows);
                
                let self_gt_max_arrows = self > max_arrows.clone();
                if self_gt_max_arrows || other > MAX_SAFE_INTEGER {
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
                    if len <= arrows {
                        sum.array.to_mut().extend(
                            core::iter::repeat(0.0)
                            .take(arrows - len + 1)
                        );
                    }
                    sum.array.to_mut()[arrows] += 1.0;
                    return sum.normalized();
                }

                let mut factor = other.clone().trunc().to_f64();
                let fract = other.clone().fract();
                let mut ret = self.clone().arrow(arrows - 1, fract);

                let mut force_break = 0;
                while force_break < ARROW_FORCE_BREAK_THRESHOLD && factor > 0.0 && ret < OmegaNum::from_arrows(MAX_SAFE_INTEGER_F, arrows - 1) {
                    force_break += 1;
                    ret = self.clone().arrow(arrows - 1, ret);
                    factor -= 1.0;
                }
                if force_break == ARROW_FORCE_BREAK_THRESHOLD { factor = 0.0; }
                
                let len = ret.array.len();
                if len < arrows {
                    ret.array.to_mut().extend(
                        core::iter::repeat(0.0)
                        .take(arrows - len)
                    );
                }
                ret.array.to_mut()[arrows - 1] += factor;
                return ret.normalized();
            }
        }
    }
}



impl fmt::Display for OmegaNum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.array.is_empty() {
            return write!(f, "{}", self.base);
        }
        if self.base < 0.0 {
            write!(f, "-")?;
            return write!(f, "{}", self.abs());
        }
        for (idx, entry) in self.array.iter().enumerate().rev() {
            let operand = if idx >= DISP_MAX_ARROWS {
                // format! isn't available without std
                let mut s = String::new();
                write!(&mut s, "{{{idx}}}")?;
                s
            } else {
                "^".repeat(idx)
            };
            if *entry == 1.0 {
                write!(f, "10{operand}")?;
            } else if *entry != 0.0 {
                write!(f, "(10{operand})^{entry}")?;
            }
        }

        if self.array[0] < 8.0 {
            write!(f, "{}{}", "e".repeat(self.array[0] as usize), self.base)
        } else {
            write!(f, "10^^{} {}", self.array[0], self.base)
        }
    }
}

impl core::fmt::Display for FromStrError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IncorrectRadix(radix) =>
                write!(f, "can only decode numbers of radix 10 (got {radix})"),
            Self::MalformedInput(index) =>
                write!(f, "malformed input at character {index}")
        }
    }
}

#[cfg(any(feature = "std", feature = "error_in_core"))]
impl Error for FromStrError {}

impl Num for OmegaNum {
    type FromStrRadixErr = FromStrError;

    fn from_str_radix(string: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        use FromStrError::*;
        if radix != 10 { return Err(IncorrectRadix(radix)); }
        
        Self::from_str(string)
    }
}

impl FromStr for OmegaNum {
    type Err = FromStrError;

    fn from_str(string: &str) -> Result<Self, Self::Err> {
        let parsed = parsing::parse_omeganum(
            &mut parsing::ParseHead::new(string)?
        )?;
        Ok(parsed)
    }
}