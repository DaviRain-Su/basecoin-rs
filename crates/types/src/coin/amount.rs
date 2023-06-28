//! Contains the `Amount` type, which represents amounts of tokens transferred.

use crate::errors::Error;
use derive_more::{Display, From, Into};
use primitive_types::U256;
use serde::{Deserialize, Serialize};
use std::str::FromStr;

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
}

impl AsRef<U256> for Amount {
    fn as_ref(&self) -> &U256 {
        &self.0
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
