use num_traits::{ConstOne, ConstZero, ToPrimitive};
use omeganum::OmegaNum;
use std::borrow::Cow;

#[test]
fn test_norm() {
    assert_eq!(
        OmegaNum::from_parts(10_000_000_000.0, Cow::Borrowed(&[0.0])).normalized(),
        OmegaNum::from_parts(10_000_000_000.0, Cow::Borrowed(&[]))
    )
}

#[test]
fn test_ops() {
    
    const TEN_E_TWENTY: OmegaNum = OmegaNum::from_parts(
        20.0, Cow::Borrowed(&[1.0])
    );
    const TEN_E_NINETEEN: OmegaNum = OmegaNum::from_parts(
        19.0, Cow::Borrowed(&[1.0])
    );
    assert_eq!(TEN_E_TWENTY + TEN_E_TWENTY, OmegaNum::from_parts(
        20.30102999566398, Cow::Borrowed(&[1.0])
    ));
    assert!(
        OmegaNum::from_parts(
            1.0,
            Cow::Borrowed(&[9e15])
        ).normalized() > TEN_E_TWENTY
    );

    let big_l = OmegaNum::from_arrows(2.0, 4);
    assert_eq!(
        big_l.clone(),
        OmegaNum::from_parts(
            10_000_000_000.0,
            Cow::Borrowed(&[8., 8.])
        ).normalized()
    );
    let big_r = OmegaNum::from_arrows(3.7, 4);
    assert_eq!(
        big_r.clone(),
        OmegaNum::from_parts(
            10_000_000_000.0,
            Cow::Borrowed(&[8., 8., 1.7000000000000002])
        ).normalized()
    );

    let small_l = omeganum::constant!(2.0);
    let small_r = omeganum::constant!(3.1);
    let small_sum = omeganum::constant!(5.1);
    let small_prod = omeganum::constant!(6.2);
    let small_diff = omeganum::constant!(-1.1);

    assert_eq!(big_l.clone() + small_r.clone(), big_l);
    assert_eq!(small_l.clone() + big_r.clone(), big_r);
    assert_eq!(small_l.clone() + small_r.clone(), small_sum);
    assert_eq!(small_l.clone() + -small_r.clone(), small_diff);
    assert_eq!(-small_r.clone() + small_l.clone(), small_diff);
    assert_eq!(big_l.clone() + big_r.clone(), big_r.clone());

    assert!((big_l.clone() + OmegaNum::NAN).is_nan());
    assert!((OmegaNum::NAN + big_r.clone()).is_nan());

    assert_eq!(OmegaNum::INFINITY + OmegaNum::INFINITY, OmegaNum::INFINITY);
    assert_eq!(
        OmegaNum::NEG_INFINITY + OmegaNum::NEG_INFINITY,
        OmegaNum::NEG_INFINITY
    );
    assert!((OmegaNum::INFINITY + OmegaNum::NEG_INFINITY).is_nan());

    assert!((OmegaNum::INFINITY - OmegaNum::INFINITY).is_nan());
    assert_eq!(OmegaNum::ZERO - 1, -1);
    assert_eq!(1 - OmegaNum::ZERO, 1);
    assert_eq!(-OmegaNum::ONE - 1, -2);
    assert_eq!(OmegaNum::ONE - -1, 2);
    assert_eq!(TEN_E_TWENTY * TEN_E_TWENTY, OmegaNum::from_parts(40.0, Cow::Borrowed(&[1.0])));
    assert_eq!(OmegaNum::from_parts(40.0, Cow::Borrowed(&[1.0])).sqrt(), TEN_E_TWENTY);

    assert_eq!(TEN_E_TWENTY - TEN_E_TWENTY, 0);
    assert_eq!(big_l.clone() - big_r.clone(), -big_r.clone());
    assert_eq!(TEN_E_TWENTY - TEN_E_NINETEEN, OmegaNum::from_parts(
        19.954242509439325, Cow::Borrowed(&[1.])
    ));

    assert_eq!(OmegaNum::from(2).arrow(0, 3), 6);
    assert_eq!(OmegaNum::from(2).arrow(1, 3), 8);
    assert_eq!(OmegaNum::from(2).arrow(2, 3), 16);
    assert_eq!(OmegaNum::from(2).arrow(3, 3), 65536);
    assert_eq!(OmegaNum::from(2).arrow(4, 3), OmegaNum::from_parts(
        19727.780405607016, Cow::Borrowed(&[65532.])
    ));
    assert_eq!(OmegaNum::from(2).arrow(5, 3), OmegaNum::from_parts(
        19727.780405607016, Cow::Borrowed(&[65532., 0., 1.])
    ));
    assert_eq!(OmegaNum::from(2).arrow(256, 2), 4);

    assert_eq!(OmegaNum::from(-2).arrow(0, 3), -6);
    assert_eq!(OmegaNum::from(-2).arrow(1, 3), -8);
    assert!(OmegaNum::from(-2).arrow(2, 3).is_nan());

    assert_eq!(OmegaNum::from(50).arrow(5, 0), 1);
    assert_eq!(OmegaNum::from(50).arrow(5, 1), 50);
    assert_eq!(OmegaNum::from(50).arrow(5, 2), OmegaNum::from(50).arrow(4, 50));

    assert_eq!(
        TEN_E_TWENTY.arrow(5, 4e20),
        OmegaNum::from_parts(
            20.602059991327963,
            Cow::Borrowed(&[1.0, 0.0, 0.0, 0.0, 1.0])
        )
    );


    assert_eq!(big_l.clone() * small_r.clone(), big_l);
    assert_eq!(small_l.clone() * big_r.clone(), big_r);
    assert_eq!(small_l.clone() * small_r.clone(), small_prod.clone());
    assert_eq!(small_l.clone() * -small_r.clone(), -small_prod.clone());
    assert_eq!(-small_r.clone() * small_l.clone(), -small_prod.clone());
    assert_eq!(-small_r.clone() * -small_l.clone(), small_prod.clone());
    assert_eq!(-small_l.clone() * big_r.clone(), -big_r.clone());
    assert_eq!(small_l.clone() * -big_r.clone(), -big_r.clone());
    assert_eq!(-big_l.clone() * small_r.clone(), -big_l.clone());
    assert_eq!(big_l.clone() * -small_r.clone(), -big_l.clone());
    assert_eq!(big_l.clone() * big_r.clone(), big_r.clone());
    assert_eq!(big_l.clone() * -big_r.clone(), -big_r.clone());
    assert_eq!(-big_l.clone() * big_r.clone(), -big_r.clone());
    assert_eq!(-big_l.clone() * -big_r.clone(), big_r.clone());

    assert!((OmegaNum::NEG_ZERO * omeganum::constant!(1)).is_negative());
    assert_eq!(1 * OmegaNum::INFINITY, OmegaNum::INFINITY);
    assert_eq!(1 * OmegaNum::INFINITY, OmegaNum::INFINITY);
    assert!((OmegaNum::NAN * 1f64).is_nan());

    assert_eq!(
        OmegaNum::INFINITY * OmegaNum::NEG_INFINITY,
        OmegaNum::NEG_INFINITY
    );
    assert_eq!(
        OmegaNum::NEG_INFINITY * OmegaNum::NEG_INFINITY,
        OmegaNum::INFINITY
    );
    assert!((OmegaNum::ZERO * OmegaNum::INFINITY).is_nan());

    assert_eq!(-OmegaNum::ONE, -1);
    assert_ne!(-OmegaNum::ONE, 1);

    assert_eq!(big_l.clone() / big_r.clone(), OmegaNum::ZERO);
    assert_eq!(big_r.clone() / big_l.clone(), big_r.clone());
    assert_eq!(-big_r.clone() / big_l.clone(), -big_r.clone());
    assert_eq!(big_r.clone() / -big_l.clone(), -big_r.clone());
    assert_eq!(-big_r.clone() / -big_l.clone(), big_r.clone());
    assert_eq!(big_l.clone() / 0, OmegaNum::INFINITY);
    assert_eq!(-big_l.clone() / 0, OmegaNum::NEG_INFINITY);
    assert!((OmegaNum::ZERO / 0f64).is_nan());
    assert!((OmegaNum::NAN / 1f64).is_nan());
    assert_eq!(OmegaNum::INFINITY / 17, OmegaNum::INFINITY);
    assert_eq!(17 / OmegaNum::INFINITY, 0);
    assert_eq!(TEN_E_TWENTY / TEN_E_NINETEEN, 10);

    assert_eq!(OmegaNum::from(5) % 3, 2);
    assert!((OmegaNum::NAN % 1f64).is_nan());
    assert!((1f64 % OmegaNum::NAN).is_nan());
    assert_eq!(TEN_E_TWENTY % 0, 0);
    assert_eq!(TEN_E_TWENTY % 1, 0);
    assert_eq!(TEN_E_NINETEEN % TEN_E_TWENTY, TEN_E_NINETEEN);
    assert_eq!(-TEN_E_NINETEEN % TEN_E_TWENTY, -TEN_E_NINETEEN);
    assert_eq!(TEN_E_NINETEEN % -TEN_E_TWENTY, -TEN_E_NINETEEN);
    assert_eq!(-TEN_E_NINETEEN % -TEN_E_TWENTY, TEN_E_NINETEEN);
    assert_eq!(TEN_E_TWENTY % 33, 0);

    assert_eq!(OmegaNum::ZERO.pow(OmegaNum::ZERO), OmegaNum::ONE);
    assert_eq!(small_l.clone().pow(small_r.clone()), omeganum::constant!(8.574187700290345));
    assert_eq!(big_l.clone().pow(big_r.clone()), big_r.clone());
    assert_eq!(big_l.clone().pow(OmegaNum::ZERO), 1);
    assert_eq!(big_l.clone().pow(-OmegaNum::ONE), 0);
    assert_eq!(OmegaNum::INFINITY.pow(OmegaNum::ZERO), 1);



    assert_ne!(omeganum::constant!(10), 0);
    assert_ne!(omeganum::constant!(10), OmegaNum::ZERO);
    assert_eq!(omeganum::constant!(10).log10(), 1);
    assert_eq!(big_l.clone().exp10(), omeganum::constant!(10).pow(big_l.clone()));
    assert_eq!(big_l.clone().log10(), big_l.clone().log(omeganum::constant!(10)));
    
    assert_eq!(big_l.clone().arrow(5, 1), big_l.clone());

    assert!(omeganum::constant!(-1).log10().is_nan());
    assert_eq!(OmegaNum::ZERO.log10(), OmegaNum::NEG_INFINITY);

}

#[test]
fn test_cmp() {
    const BIG: OmegaNum = OmegaNum::from_parts(
        10_000_000_000.0, Cow::Borrowed(&[8.0, 8.0, 1.0])
    );
    const BIGGER: OmegaNum = OmegaNum::from_parts(
        10_000_000_000.0, Cow::Borrowed(&[8.0, 8.0, 1.2])
    );
    const BIGGERER: OmegaNum = OmegaNum::from_parts(
        10_000_000_000.0, Cow::Borrowed(&[8.0, 8.0, 8.0, 1.0])
    );
    
    assert!(OmegaNum::NAN != OmegaNum::NAN);
    assert!(!(OmegaNum::NAN < OmegaNum::NAN));
    assert!(!(OmegaNum::NAN > OmegaNum::NAN));
    assert!(OmegaNum::INFINITY == OmegaNum::INFINITY);
    assert!(OmegaNum::ZERO == OmegaNum::ZERO);
    assert!(OmegaNum::ONE == OmegaNum::ONE);
    assert!(OmegaNum::ONE > OmegaNum::ZERO);
    assert!(OmegaNum::ZERO < OmegaNum::ONE);

    assert!(OmegaNum::ONE > -OmegaNum::ONE);
    assert!(1 < BIG);
    assert!(-1 < BIG);
    assert!(BIG > -1);
    assert!(BIG > 1);
    assert!(BIG == BIG);
    assert!(OmegaNum::INFINITY > BIG);
    assert!(OmegaNum::NEG_INFINITY < BIG);
    assert!(BIG < OmegaNum::INFINITY);
    assert!(BIG > OmegaNum::NEG_INFINITY);
    assert!(BIGGER > BIG);
    assert!(BIG < BIGGER);
    assert!(-BIGGER < -BIG);
    assert!(-BIG > -BIGGER);
    assert!(BIGGERER > BIG);
    assert!(BIGGERER >= BIGGERER);
    assert!(BIG < BIGGERER);
    assert!(-BIGGERER < -BIG);
    assert!(-BIG > -BIGGERER);
}

#[test]
fn test_ident() {
    let big = OmegaNum::from_arrows(2.0, 4);

    assert!(OmegaNum::ONE.is_simple());
    assert!(!big.is_simple());
    assert!(OmegaNum::ONE.is_finite());
    assert!(!OmegaNum::NAN.is_finite());
    assert!(!OmegaNum::INFINITY.is_finite());
    assert!(!OmegaNum::ONE.is_infinite());
    assert!(OmegaNum::INFINITY.is_infinite());
    assert!(!OmegaNum::NAN.is_infinite());
    assert!(!OmegaNum::INFINITY.is_integer());
    assert!(!OmegaNum::NAN.is_integer());
    assert!(OmegaNum::ONE.is_integer());
    assert!(!omeganum::constant!(1.5).is_integer());
    assert!(big.is_integer());
}

#[test]
fn test_conv() {
    assert_eq!(f64::from(OmegaNum::ONE), 1.0_f64);
    assert_eq!(ToPrimitive::to_f64(&OmegaNum::ONE), Some(1.0_f64));
    assert_eq!(ToPrimitive::to_i64(&OmegaNum::ONE), Some(1));
    assert_eq!(ToPrimitive::to_u64(&OmegaNum::ONE), Some(1));

    let big = OmegaNum::from_arrows(2.0, 8);

    assert_eq!(big.to_f64(), f64::INFINITY);
}

#[test]
fn test_parse() {
    assert_eq!("0".parse::<OmegaNum>().unwrap(), 0);
    assert_eq!("17".parse::<OmegaNum>().unwrap(), 17);
    assert_eq!("-13.73".parse::<OmegaNum>().unwrap(), -13.73);
    assert_eq!("10{5}4.3e9".parse::<OmegaNum>().unwrap(), OmegaNum::from_arrows(4.3e9, 5));
    assert_eq!("10^^^2".parse::<OmegaNum>().unwrap(), OmegaNum::from_arrows(2., 3));
    assert_eq!("Infinity".parse::<OmegaNum>().unwrap(), OmegaNum::INFINITY);
    assert_eq!("-Infinity".parse::<OmegaNum>().unwrap(), OmegaNum::NEG_INFINITY);
    assert!("NaN".parse::<OmegaNum>().unwrap().is_nan());
    assert!("".parse::<OmegaNum>().is_err());
    assert!("Na".parse::<OmegaNum>().is_err());
    assert!("-".parse::<OmegaNum>().is_err());
    assert!("+".parse::<OmegaNum>().is_err());
    assert!("01".parse::<OmegaNum>().is_err());
    assert!("10{4".parse::<OmegaNum>().is_err());
    assert!("10{}4".parse::<OmegaNum>().is_err());
    assert!("10{1}".parse::<OmegaNum>().is_err());
    assert!("10^^^".parse::<OmegaNum>().is_err());
    assert!("10{1}4e".parse::<OmegaNum>().is_err());
    assert!("10{1}4e-".parse::<OmegaNum>().is_err());
    assert!("10{1}4e+".parse::<OmegaNum>().is_err());
    assert!("10{1}4e05".parse::<OmegaNum>().is_err());
    assert!("10^^^e9".parse::<OmegaNum>().is_err());
}
