#![deny(missing_docs)]
//! The finite field used in the language.
//!
//! This defines the LurkField trait used pervasively in the code base
//! as an extension of the ff::PrimeField trait, with convenience methods
//! relating this field to the expressions of the language.
use clap::ValueEnum;
use ff::{PrimeField, PrimeFieldBits};
use halo2curves::bn256::Fr as Bn256Scalar;
use halo2curves::grumpkin::Fr as GrumpkinScalar;
use serde::{Deserialize, Serialize};
use std::convert::TryFrom;
use std::hash::Hash;

use crate::tag::{ContTag, ExprTag, Op1, Op2};

/// The type of finite fields used in the language
/// For Pallas/Vesta see `<https://electriccoin.co/blog/the-pasta-curves-for-halo-2-and-beyond/>`
///
/// Please note:
/// - pasta_curves::pallas::Scalar = pasta_curves::Fq
/// - pasta_curves::vesta::Scalar = pasta_curves::Fp
///
/// Because confusion on this point, perhaps combined with cargo-cult copying of incorrect previous usage has led to
/// inconsistencies and inaccuracies in the code base, please prefer the named Scalar forms when correspondence to a
/// named `LanguageField` is important.
#[derive(Default, Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, ValueEnum)]
#[clap(rename_all = "lowercase")]
pub enum LanguageField {
    /// The BN256 scalar field,
    #[default]
    BN256,
    /// THe Grumpkin scalar field,
    Grumpkin,
    /// The Pallas field,
    Pallas,
    /// The Vesta field,
    Vesta,
}

impl std::fmt::Display for LanguageField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Pallas => write!(f, "pallas"),
            Self::Vesta => write!(f, "vesta"),
            Self::BN256 => write!(f, "bn256"),
            Self::Grumpkin => write!(f, "grumpkin"),
        }
    }
}

/// Trait implemented by finite fields used in the language
pub trait LurkField: PrimeField + PrimeFieldBits {
    /// The type of the field element's representation
    const FIELD: LanguageField;

    /// The default secret for non-hiding commitments
    const NON_HIDING_COMMITMENT_SECRET: Self = Self::ZERO;

    /// Converts the field element to a byte vector
    fn to_bytes(&self) -> Vec<u8> {
        let repr = self.to_repr();
        repr.as_ref().to_vec()
    }
    /// Attempts to construct a field element from a byte slice
    fn from_bytes(bs: &[u8]) -> Option<Self> {
        let mut def: Self::Repr = Self::default().to_repr();
        def.as_mut().copy_from_slice(bs);
        Self::from_repr(def).into()
    }

    /// Converts the field element to a hexadecimal string
    fn hex_digits(&self) -> String {
        let bytes = self.to_bytes();
        let mut s = String::with_capacity(bytes.len() * 2);
        for b in bytes.iter().rev() {
            s.push_str(&format!("{b:02x?}"));
        }
        s
    }

    /// Converts the field to a variable-length hex string
    fn trimmed_hex_digits(self) -> String {
        let hex_digits = &self.hex_digits();
        let mut res = hex_digits.trim_start_matches('0');
        if res.is_empty() {
            res = "0";
        }
        res.to_owned()
    }

    /// Attempts to convert the field element to a u16
    fn to_u16(&self) -> Option<u16> {
        for x in &self.to_repr().as_ref()[2..] {
            if *x != 0 {
                return None;
            }
        }
        let mut byte_array = [0u8; 2];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..2]);
        Some(u16::from_le_bytes(byte_array))
    }

    /// Attempts to convert the field element to a u32
    fn to_u32(&self) -> Option<u32> {
        for x in &self.to_repr().as_ref()[4..] {
            if *x != 0 {
                return None;
            }
        }
        let mut byte_array = [0u8; 4];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..4]);
        Some(u32::from_le_bytes(byte_array))
    }

    /// Attempts to convert the field element to a char
    fn to_char(&self) -> Option<char> {
        let x = self.to_u32()?;
        char::from_u32(x)
    }

    /// Attempts to convert the field element to a u64
    fn to_u64(&self) -> Option<u64> {
        for x in &self.to_repr().as_ref()[8..] {
            if *x != 0 {
                return None;
            }
        }
        let mut byte_array = [0u8; 8];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..8]);
        Some(u64::from_le_bytes(byte_array))
    }

    /// Attempts to convert the field element to a u64
    fn to_u128(&self) -> Option<u128> {
        for x in &self.to_repr().as_ref()[16..] {
            if *x != 0 {
                return None;
            }
        }
        let mut byte_array = [0u8; 16];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..16]);
        Some(u128::from_le_bytes(byte_array))
    }

    /// Converts the first 4 bytes of the field element to a u32
    fn to_u32_unchecked(&self) -> u32 {
        let mut byte_array = [0u8; 4];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..4]);
        u32::from_le_bytes(byte_array)
    }

    /// Converts the first 8 bytes of the field element to a u64
    fn to_u64_unchecked(&self) -> u64 {
        let mut byte_array = [0u8; 8];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..8]);
        u64::from_le_bytes(byte_array)
    }

    /// Converts the first 16 bytes of the field element to a u128
    fn to_u128_unchecked(&self) -> u128 {
        let mut byte_array = [0u8; 16];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..16]);
        u128::from_le_bytes(byte_array)
    }

    /// Constructs a field element from a u64
    fn from_u64(x: u64) -> Self {
        x.into()
    }

    /// Constructs a field element from a u32
    fn from_u32(x: u32) -> Self {
        u64::from(x).into()
    }
    /// Constructs a field element from a u16
    fn from_u16(x: u16) -> Self {
        u64::from(x).into()
    }
    /// Constructs a field element from a char
    fn from_char(x: char) -> Self {
        Self::from_u32(x as u32)
    }

    /// We define this to be the smallest negative field element
    fn most_negative() -> Self {
        Self::most_positive() + Self::ONE
    }

    /// 0 - 1 is one minus the modulus, which must be even in a prime field.
    /// The result is the largest field element which is even when doubled.
    /// We define this to be the most positive field element.
    fn most_positive() -> Self {
        let one = Self::ONE;
        let two = one + one;

        let half = two.invert().unwrap();
        let modulus_minus_one = Self::ZERO - one;
        half * modulus_minus_one
    }

    /// A field element is defined to be negative if it is odd after doubling.
    fn is_negative(&self) -> bool {
        self.double().is_odd().into()
    }

    /// Constructs a field element from an ExprTag
    fn from_expr_tag(tag: ExprTag) -> Self {
        Self::from_u64(tag.into())
    }
    /// Attempts to convert the field element to an ExprTag
    fn to_expr_tag(&self) -> Option<ExprTag> {
        let x = Self::to_u16(self)?;
        ExprTag::try_from(x).ok()
    }

    /// Constructs a field element from a ContTag
    fn from_cont_tag(tag: ContTag) -> Self {
        Self::from_u64(tag.into())
    }

    /// Attempts to convert the field element to a ContTag
    fn to_cont_tag(&self) -> Option<ContTag> {
        let x = Self::to_u16(self)?;
        ContTag::try_from(x).ok()
    }
    /// Constructs a field element from an Op1
    fn from_op1(tag: Op1) -> Self {
        Self::from_u64(tag.into())
    }

    /// Attempts to convert the field element to an Op1
    fn to_op1(&self) -> Option<Op1> {
        let x = Self::to_u16(self)?;
        Op1::try_from(x).ok()
    }
    /// Constructs a field element from an Op2
    fn from_op2(tag: Op2) -> Self {
        Self::from_u64(tag.into())
    }

    /// Attempts to convert the field element to an Op2
    fn to_op2(&self) -> Option<Op2> {
        let x = Self::to_u16(self)?;
        Op2::try_from(x).ok()
    }

    /// Returns the LanguageField of the field
    fn get_field(&self) -> LanguageField {
        Self::FIELD
    }
}

impl LurkField for pasta_curves::pallas::Scalar {
    const FIELD: LanguageField = LanguageField::Pallas;
}

impl LurkField for pasta_curves::vesta::Scalar {
    const FIELD: LanguageField = LanguageField::Vesta;
}

impl LurkField for Bn256Scalar {
    const FIELD: LanguageField = LanguageField::BN256;
}

impl LurkField for GrumpkinScalar {
    const FIELD: LanguageField = LanguageField::Grumpkin;
}

// The impl LurkField for grumpkin::Scalar is technically possible, but voluntarily omitted to avoid confusion.

// For working around the orphan trait impl rule
/// Wrapper struct around a field element that implements additional traits
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FWrap<F>(pub F);

impl<F: LurkField> Copy for FWrap<F> {}

#[allow(clippy::derived_hash_with_manual_eq)]
impl<F: LurkField> Hash for FWrap<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_repr().as_ref().hash(state);
    }
}

impl<F: LurkField> PartialOrd for FWrap<F> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: LurkField> Ord for FWrap<F> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        (self.0.to_repr().as_ref()).cmp(other.0.to_repr().as_ref())
    }
}

impl<F: LurkField> Serialize for FWrap<F> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let bytes: Vec<u8> = Vec::from(self.0.to_repr().as_ref());
        bytes.serialize(serializer)
    }
}

impl<'de, F: LurkField> Deserialize<'de> for FWrap<F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::Error;
        let bytes: Vec<u8> = Vec::deserialize(deserializer)?;
        let f = F::from_bytes(&bytes).ok_or_else(|| {
            D::Error::custom(format!("expected field element as bytes, got {:?}", &bytes))
        })?;
        Ok(FWrap(f))
    }
}
