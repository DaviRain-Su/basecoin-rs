//! Contains the `Amount` type, which represents amounts of tokens transferred.

use crate::errors::Error;
use derive_more::{Display, From, Into};
use primitive_types::U256;
use serde::{Deserialize, Serialize};
use std::{
    ops::{Add, Div, Mul, Sub},
    str::FromStr,
};

/// A type for representing token transfer amounts.
#[derive(
    Serialize, Deserialize, Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Display, From, Into,
)]
pub struct Amount(U256);

impl Amount {
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.0.checked_add(rhs.0).map(Self)
    }

    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.0.checked_sub(rhs.0).map(Self)
    }

    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    pub fn zero() -> Self {
        Self(U256::zero())
    }

    pub fn is_positive(&self) -> bool {
        self.0 >= U256::zero()
    }
}

impl AsRef<U256> for Amount {
    fn as_ref(&self) -> &U256 {
        &self.0
    }
}

impl Add for Amount {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl Sub for Amount {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0 - rhs.0)
    }
}

impl Mul<u64> for Amount {
    type Output = Self;

    fn mul(self, rhs: u64) -> Self::Output {
        Self(self.0 * <u64 as Into<u64>>::into(rhs))
    }
}

impl Div<u64> for Amount {
    type Output = Self;

    fn div(self, rhs: u64) -> Self::Output {
        Self(self.0 / <u64 as Into<u64>>::into(rhs))
    }
}

impl FromStr for Amount {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let amount = U256::from_dec_str(s).map_err(|e| Error::InvalidAmount(e.to_string()))?;
        Ok(Self(amount))
    }
}

impl From<u64> for Amount {
    fn from(v: u64) -> Self {
        Self(v.into())
    }
}
