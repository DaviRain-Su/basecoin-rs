//! Defines coin types; the objects that are being transferred.

use crate::errors::Error;
use anyhow::Result;
use ibc_proto::cosmos::base::v1beta1::Coin as RawBaseCoin;
use ibc_proto::cosmos::base::v1beta1::Coin as ProtoCoin;
use ibc_proto::google::protobuf::Any;
use ibc_proto::protobuf::Protobuf;
use safe_regex::regex;
use serde_derive::{Deserialize, Serialize};
use std::fmt::{Display, Error as FmtError, Formatter};
use std::ops::{Add, Index, Sub};
use std::str::{from_utf8, FromStr};

use crate::coin::amount::Amount;
use crate::coin::denom::{BaseDenom, PrefixedDenom};
use crate::serializers::serde_string;
use regex::Regex;

pub mod amount;
pub mod denom;

pub const TYPE_URL: &str = "/cosmos.base.v1beta1.Coin";

/// A `Coin` type with fully qualified `PrefixedDenom`.
pub type PrefixedCoin = Coin<PrefixedDenom>;

/// A `Coin` type with an unprefixed denomination.
pub type BaseCoin = Coin<BaseDenom>;

/// Coin defines a token with a denomination and an amount.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct Coin<D> {
    /// Denomination
    pub denom: D,
    /// Amount
    #[serde(with = "serde_string")]
    pub amount: Amount,
}

impl<D: FromStr> Coin<D>
where
    D::Err: Into<Error>,
{
    pub fn from_string_list(coin_str: &str) -> Result<Vec<Self>, Error> {
        coin_str.split(',').map(FromStr::from_str).collect()
    }
}

impl<D: FromStr> FromStr for Coin<D>
where
    D::Err: Into<Error>,
{
    type Err = Error;

    #[allow(clippy::assign_op_pattern)]
    fn from_str(coin_str: &str) -> Result<Self, Error> {
        // Denominations can be 3 ~ 128 characters long and support letters, followed by either
        // a letter, a number or a separator ('/', ':', '.', '_' or '-').
        // Loosely copy the regex from here:
        // https://github.com/cosmos/cosmos-sdk/blob/v0.45.5/types/coin.go#L760-L762
        let matcher = regex!(br"([0-9]+)([a-zA-Z0-9/:\\._\x2d]+)");

        let (m1, m2) =
            matcher
                .match_slices(coin_str.as_bytes())
                .ok_or_else(|| Error::InvalidCoin {
                    coin: coin_str.to_string(),
                })?;

        let amount = from_utf8(m1).map_err(Error::Utf8Decode)?.parse()?;

        let denom = from_utf8(m2)
            .map_err(Error::Utf8Decode)?
            .parse()
            .map_err(Into::into)?;

        Ok(Coin { amount, denom })
    }
}

impl<D: FromStr> TryFrom<ProtoCoin> for Coin<D>
where
    D::Err: Into<Error>,
{
    type Error = Error;

    fn try_from(proto: ProtoCoin) -> Result<Coin<D>, Self::Error> {
        let denom = D::from_str(&proto.denom).map_err(Into::into)?;
        let amount = Amount::from_str(&proto.amount)?;
        Ok(Self { denom, amount })
    }
}

impl<D: ToString> From<Coin<D>> for ProtoCoin {
    fn from(coin: Coin<D>) -> ProtoCoin {
        ProtoCoin {
            denom: coin.denom.to_string(),
            amount: coin.amount.to_string(),
        }
    }
}

impl From<BaseCoin> for PrefixedCoin {
    fn from(coin: BaseCoin) -> PrefixedCoin {
        PrefixedCoin {
            denom: coin.denom.into(),
            amount: coin.amount,
        }
    }
}

impl<D: Display> Display for Coin<D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "{}{}", self.amount, self.denom)
    }
}

// BaseCoin is a Coin with a BaseDenom.
impl ibc_proto::protobuf::Protobuf<RawBaseCoin> for BaseCoin {}

impl From<BaseCoin> for Any {
    fn from(coin: BaseCoin) -> Self {
        Any {
            type_url: TYPE_URL.to_string(),
            value: coin.encode_vec(),
        }
    }
}

impl BaseCoin {
    pub fn new(denom: String, amount: u64) -> Result<Self> {
        let coin = Self {
            denom: BaseDenom::from_str(denom.as_str())?,
            amount: amount.into(),
        };

        coin.validate()?;

        Ok(coin)
    }

    /// `validate` returns an error if the Coin has a negative amount or if
    /// the denom is invalid.
    fn validate(&self) -> Result<()> {
        validate_denom(self.denom.as_str())?;
        Ok(())
    }

    /// `is_valid` returns true if the Coin has a non-negative amount and the denom is valid.
    pub fn is_valid(&self) -> bool {
        self.validate().is_ok()
    }

    /// `is_zero` returns if this represents no money
    pub fn is_zero(&self) -> bool {
        self.amount.is_zero()
    }

    // `is_gte` returns true if they are the same type and the receiver is
    // an equal or greater value
    pub fn is_gte(&self, other: BaseCoin) -> bool {
        if self.denom != other.denom {
            panic!(
                "invalid coin denominations; {} != {}",
                self.denom, other.denom
            );
        }

        !self.amount.lt(&other.amount)
    }

    // `is_lt` returns true if they are the same type and the receiver is
    // a smaller value
    pub fn is_lt(&self, other: BaseCoin) -> bool {
        if self.denom != other.denom {
            panic!(
                "invalid coin denominations; {} != {}",
                self.denom, other.denom
            );
        }

        self.amount.lt(&other.amount)
    }
    // `is_lte` returns true if they are the same type and the receiver is
    // an equal or smaller value
    pub fn is_lte(&self, other: BaseCoin) -> bool {
        if self.denom != other.denom {
            panic!(
                "invalid coin denominations; {} != {}",
                self.denom, other.denom
            );
        }

        !self.amount.gt(&other.amount)
    }

    // `is_equal` returns true if the two sets of Coins have the same value
    // Deprecated: Use Coin.Equal instead.
    pub fn is_equal(&self, other: BaseCoin) -> bool {
        self.denom == other.denom && self.amount == other.amount
    }

    /// AddAmount adds an amount to the Coin.
    pub fn add_amount(&self, amount: Amount) -> Self {
        Self {
            denom: self.denom.clone(),
            amount: self.amount.add(amount),
        }
    }

    /// `sub_amount` subtracts an amount from the Coin.
    pub fn sub_amount(&self, amount: Amount) -> Self {
        Self {
            denom: self.denom.clone(),
            amount: self.amount.sub(amount),
        }
    }
}

/// `add` adds amounts of two coins with same denom. If the coins differ in denom then
/// it panics.
impl Add for BaseCoin {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        if self.denom != other.denom {
            panic!(
                "invalid coin denominations; {} != {}",
                self.denom, other.denom
            );
        }

        Self {
            denom: self.denom,
            amount: self.amount.add(other.amount),
        }
    }
}

/// Sub subtracts amounts of two coins with same denom and panics on error.
impl Sub for BaseCoin {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        if self.denom != other.denom {
            panic!(
                "invalid coin denominations; {} != {}",
                self.denom, other.denom
            );
        }

        Self {
            denom: self.denom,
            amount: self.amount.sub(other.amount),
        }
    }
}

pub fn validate_denom(denom: &str) -> Result<(), Error> {
    let coin_denom_regex = default_coin_denom_regex();
    let matcher = Regex::new(&format!("^{}$", coin_denom_regex)).unwrap();

    if let Some(captures) = matcher.captures(denom) {
        tracing::info!("captures = {:?}", captures.index(0));
    } else {
        return Err(Error::InvalidCoin {
            coin: denom.to_string(),
        });
    }

    Ok(())
}

fn default_coin_denom_regex() -> String {
    String::from(r"[a-zA-Z][a-zA-Z0-9/:._-]{2,127}")
}

#[cfg(test)]
mod tests {
    use super::*;
    type RawCoin = Coin<String>;

    #[test]
    fn test_parse_raw_coin() -> Result<(), Error> {
        {
            let coin = RawCoin::from_str("123stake")?;
            assert_eq!(coin.denom, "stake");
            assert_eq!(coin.amount, 123u64.into());
        }

        {
            let coin = RawCoin::from_str("1a1")?;
            assert_eq!(coin.denom, "a1");
            assert_eq!(coin.amount, 1u64.into());
        }

        {
            let coin = RawCoin::from_str("0x1/:.\\_-")?;
            assert_eq!(coin.denom, "x1/:.\\_-");
            assert_eq!(coin.amount, 0u64.into());
        }

        {
            // `!` is not allowed
            let res = RawCoin::from_str("0x!");
            assert!(res.is_err());
        }

        Ok(())
    }

    #[test]
    fn test_parse_raw_coin_list() -> Result<(), Error> {
        {
            let coins = RawCoin::from_string_list("123stake,1a1,999den0m")?;
            assert_eq!(coins.len(), 3);

            assert_eq!(coins[0].denom, "stake");
            assert_eq!(coins[0].amount, 123u64.into());

            assert_eq!(coins[1].denom, "a1");
            assert_eq!(coins[1].amount, 1u64.into());

            assert_eq!(coins[2].denom, "den0m");
            assert_eq!(coins[2].amount, 999u64.into());
        }

        Ok(())
    }

    #[test]
    fn test_valid_denom() -> Result<()> {
        let base_coin = BaseCoin::new("stake".into(), 23)?;
        assert_eq!(base_coin.denom.as_str(), "stake");
        println!("base coin: {:?}", base_coin);
        Ok(())
    }
}
