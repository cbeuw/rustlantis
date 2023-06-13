use mir::{
    syntax::{Literal, TyId, TyKind},
    tyctxt::TyCtxt,
};
use rand::{seq::SliceRandom, Rng, RngCore};
use rand_distr::Distribution;

use crate::ty::ARRAY_MAX_LEN;

struct Sombrero;

impl Distribution<usize> for Sombrero {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        match rng.gen_range(0..=1) {
            0 => rng.gen_range(0..ARRAY_MAX_LEN),
            1 => rng.gen_range(usize::MIN..=usize::MAX),
            _ => unreachable!(),
        }
    }
}

impl Distribution<isize> for Sombrero {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> isize {
        match rng.gen_range(0..=2) {
            0 => rng.gen_range(-128..=127),
            1 => isize::MIN,
            2 => isize::MAX,
            _ => unreachable!(),
        }
    }
}

pub trait GenLiteral: Rng {
    fn is_literalble(ty: TyId, tcx: &TyCtxt) -> bool {
        match ty.kind(tcx) {
            TyKind::Unit => false,
            _ => ty.is_scalar(tcx),
        }
    }
    fn gen_literal(&mut self, ty: TyId, tcx: &TyCtxt) -> Option<Literal> {
        let lit: Literal = match ty.kind(tcx) {
            TyKind::Bool => self.gen_bool(0.5).into(),
            TyKind::Char => {
                // There are 0xD7FF + 1 Unicode Scalar Values in the lower range, and 0x10FFFF - 0xE000 + 1
                // values in the upper range.
                let ordinal = self.gen_range(0..((0xD7FF + 1) + (0x10FFFF - 0xE000 + 1)));
                if ordinal <= 0xD7FF {
                    char::from_u32(ordinal).unwrap().into()
                } else {
                    char::from_u32(ordinal - 0xD800 + 0xE000).unwrap().into()
                }
            }
            &TyKind::USIZE => {
                let i: usize = Sombrero.sample(self);
                i.try_into().expect("usize isn't greater than 128 bits")
            }
            &TyKind::U8 => self.gen_range(u8::MIN..=u8::MAX).into(),
            &TyKind::U16 => self.gen_range(u16::MIN..=u16::MAX).into(),
            &TyKind::U32 => self.gen_range(u32::MIN..=u32::MAX).into(),
            &TyKind::U64 => self.gen_range(u64::MIN..=u64::MAX).into(),
            &TyKind::U128 => self.gen_range(u128::MIN..=u128::MAX).into(),
            &TyKind::ISIZE => {
                let i: isize = Sombrero.sample(self);
                i.try_into().expect("isize isn't greater than 128 bits")
            }
            &TyKind::I8 => self.gen_range(i8::MIN..=i8::MAX).into(),
            &TyKind::I16 => self.gen_range(i16::MIN..=i16::MAX).into(),
            &TyKind::I32 => self.gen_range(i32::MIN..=i32::MAX).into(),
            &TyKind::I64 => self.gen_range(i64::MIN..=i64::MAX).into(),
            &TyKind::I128 => self.gen_range(i128::MIN..=i128::MAX).into(),
            &TyKind::F32 => generate_f32(self).into(),
            &TyKind::F64 => generate_f64(self).into(),
            _ => return None,
        };
        Some(lit)
    }
    fn gen_literal_non_zero(&mut self, ty: TyId, tcx: &TyCtxt) -> Option<Literal> {
        self.gen_literal(ty, tcx).map(|lit| match lit {
            Literal::Uint(n, t) => {
                if n == 0 {
                    Literal::Uint(n + 1, t)
                } else {
                    lit
                }
            }
            Literal::Int(n, t) => {
                if n == 0 {
                    Literal::Int(n + 1, t)
                } else {
                    lit
                }
            }
            Literal::Float(n, t) => {
                if n == 0. {
                    Literal::Float(n + 1., t)
                } else {
                    lit
                }
            }
            _ => lit,
        })
    }
}

impl<R: RngCore + ?Sized> GenLiteral for R {}

enum Category {
    Normal,
    Subnormal,
    Zero,
    Infinity,
    NaN,
}

const FLOAT_CATEGORIES: [Category; 5] = [
    Category::Normal,
    Category::Subnormal,
    Category::Zero,
    Category::Infinity,
    Category::NaN,
];

fn generate_f32<R: Rng + ?Sized>(rng: &mut R) -> f32 {
    let chosen = FLOAT_CATEGORIES.choose(rng).unwrap();
    match chosen {
        Category::Normal => {
            let sign: u32 = *[0 << 31, 1 << 31].choose(rng).unwrap();
            let exponent = rng.gen_range(0x01..=0xfe);
            let fraction = rng.gen_range(0..(1 << 23));
            f32::from_bits(sign | exponent | fraction)
        }
        Category::Subnormal => {
            let sign: u32 = *[0 << 31, 1 << 31].choose(rng).unwrap();
            let exponent = 0 << 23;
            let fraction = rng.gen_range(1..(1 << 23));
            f32::from_bits(sign | exponent | fraction)
        }
        Category::Zero => *[0.0, -0.0].choose(rng).unwrap(),
        Category::Infinity => *[f32::INFINITY, f32::NEG_INFINITY].choose(rng).unwrap(),
        Category::NaN => f32::NAN,
    }
}

fn generate_f64<R: Rng + ?Sized>(rng: &mut R) -> f64 {
    let chosen = FLOAT_CATEGORIES.choose(rng).unwrap();
    match chosen {
        Category::Normal => {
            let sign: u64 = *[0 << 63, 1 << 63].choose(rng).unwrap();
            let exponent = rng.gen_range(0x001..=0x7fe);
            let fraction = rng.gen_range(0..(1 << 52));
            f64::from_bits(sign | exponent | fraction)
        }
        Category::Subnormal => {
            let sign: u64 = *[0 << 63, 1 << 63].choose(rng).unwrap();
            let exponent = 0 << 52;
            let fraction = rng.gen_range(1..(1 << 52));
            f64::from_bits(sign | exponent | fraction)
        }
        Category::Zero => *[0.0, -0.0].choose(rng).unwrap(),
        Category::Infinity => *[f64::INFINITY, f64::NEG_INFINITY].choose(rng).unwrap(),
        Category::NaN => f64::NAN,
    }
}
