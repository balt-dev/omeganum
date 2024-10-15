use crate::OmegaNum;

use super::Cow;



pub(crate) const TEN_BILLION: f64 = 10_000_000_000.0;
pub(crate) const MAX_SAFE_INT: u64 = (1u64 << 53) - 1;
#[doc(hidden)]
pub const EMPTY_ARRAY: Cow<'static, [f64]> = Cow::Borrowed(&[]);
#[doc(hidden)]
pub const MAX_SAFE_INTEGER_F: f64 = MAX_SAFE_INT as f64;
#[doc(hidden)]
pub const MIN_SAFE_INTEGER_F: f64 = -MAX_SAFE_INTEGER_F;
/// Self::MAX_SAFE_INTEGER.log10()
pub const MAX_E: f64 = 15.954589770191003;

/// f64::MAX.log10()
pub const LOG10_MAX: f64 = 308.25471555991675;

pub const E_MAX_SAFE_INTEGER: OmegaNum =
    OmegaNum::from_parts(MAX_SAFE_INTEGER_F, Cow::Borrowed(&[1.0]));
pub const EE_MAX_SAFE_INTEGER: OmegaNum =
    OmegaNum::from_parts(MAX_SAFE_INTEGER_F, Cow::Borrowed(&[2.0]));
pub const TETRATED_MAX_SAFE_INTEGER: OmegaNum =
    OmegaNum::from_parts(1.0, Cow::Borrowed(&[MAX_SAFE_INTEGER_F]));

pub const ARROW_FORCE_BREAK_THRESHOLD: usize = 100;
pub const DISP_MAX_ARROWS: usize = 5;
pub const DISP_MAX_E: f64 = 8.0;
