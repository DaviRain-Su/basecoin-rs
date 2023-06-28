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

    /// `add_amount` adds an amount to the Coin.
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

// --------------------------------------------------

/// Coins is a set of Coin, one per currency
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct BaseCoins(pub Vec<BaseCoin>);

impl From<Vec<BaseCoin>> for BaseCoins {
    fn from(coins: Vec<BaseCoin>) -> Self {
        Self(coins)
    }
}

pub fn sanitize_coins(coins: Vec<BaseCoin>) -> BaseCoins {
    let mut new_coins = remove_zero_coins(coins.into());
    new_coins.sort();
    new_coins
}

/// `remove_zero_coins` removes all zero coins from the given coin set in-place.
pub fn remove_zero_coins(coins: BaseCoins) -> BaseCoins {
    let mut non_zeros = Vec::with_capacity(coins.0.len());

    for coin in coins.0 {
        if !coin.is_zero() {
            non_zeros.push(coin);
        }
    }

    BaseCoins(non_zeros)
}

// Sort is a helper function to sort the set of coins in-place
impl BaseCoins {
    pub fn new(coins: Vec<BaseCoin>) -> Result<Self> {
        let new_coins = sanitize_coins(coins);
        new_coins.validate()?;
        Ok(new_coins)
    }

    // `validate` checks that the Coins are sorted, have positive amount, with a valid and unique
    // denomination (i.e no duplicates). Otherwise, it returns an error.
    pub fn validate(&self) -> Result<()> {
        match self.0.len() {
            0 => Ok(()),
            1 => {
                self.0[0].validate()?;
                Ok(())
            }
            _ => {
                let mut low_denom = self.0[0].denom.clone();

                for coin in self.0.iter().skip(1) {
                    coin.validate()?;
                    if coin.denom < low_denom {
                        return Err(anyhow::anyhow!("denomination is not sorted"));
                    }
                    if coin.denom == low_denom {
                        return Err(anyhow::anyhow!("duplicate denomination"));
                    }

                    // we compare each coin against the last denom
                    low_denom = coin.denom.clone();
                }

                Ok(())
            }
        }
    }

    pub fn sort(&mut self) {
        self.0.sort();
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn is_sorted(&self) -> bool {
        self.0.windows(2).all(|w| w[0] <= w[1])
    }

    pub fn is_valid(&self) -> bool {
        self.validate().is_ok()
    }

    // `denoms` returns all denoms associated with a Coins object
    pub fn denoms(&self) -> Vec<String> {
        self.0.iter().map(|c| c.denom.0.clone()).collect()
    }

    // `safe_add` will perform addition of two coins sets. If both coin sets are
    // empty, then an empty set is returned. If only a single set is empty, the
    // other set is returned. Otherwise, the coins are compared in order of their
    // denomination and addition only occurs when the denominations match, otherwise
    // the coin is simply added to the sum assuming it's not zero.
    // The function panics if `coins` or  `coinsB` are not sorted (ascending).
    pub fn safe_add(&self, coins_b: &BaseCoins) -> BaseCoins {
        if !self.is_sorted() {
            panic!("Coins (self) must be sorted")
        }
        if !coins_b.is_sorted() {
            panic!("Wrong argument: coins must be sorted")
        }

        let mut uniq_coins: std::collections::HashMap<BaseDenom, BaseCoin> =
            std::collections::HashMap::with_capacity(self.len() + coins_b.len());

        for coins in &[self, coins_b] {
            for coin in coins.0.iter() {
                if let Some(uc) = uniq_coins.get_mut(&coin.denom) {
                    *uc = uc.clone().add(coin.clone());
                } else {
                    uniq_coins.insert(coin.denom.clone(), coin.clone());
                }
            }
        }

        let mut coalesced = Vec::with_capacity(uniq_coins.len());
        for (_, c) in uniq_coins {
            if c.is_zero() {
                continue;
            }
            coalesced.push(c);
        }

        BaseCoins(coalesced)
    }

    // `amount_of_no_denom_validation` returns the amount of a denom from coins
    // without validating the denomination.
    pub fn amount_of_no_denom_validation(&self, denom: &str) -> Amount {
        if let Some(c) = self.find(denom) {
            c.amount
        } else {
            Amount::zero()
        }
    }

    // `amount_of` returns the amount of a denom from coins
    pub fn amount_of(&self, denom: &str) -> Amount {
        validate_denom(denom).expect("invalid denom");
        self.amount_of_no_denom_validation(denom)
    }

    // `find` returns true and coin if the denom exists in coins. Otherwise it returns false
    // and a zero coin. Uses binary search.
    // CONTRACT: coins must be valid (sorted).
    pub fn find(&self, denom: &str) -> Option<BaseCoin> {
        match self.0.len() {
            0 => None,
            1 => {
                if self.0[0].denom.0 == denom {
                    Some(self.0[0].clone())
                } else {
                    None
                }
            }
            _ => {
                let mid_idx = self.0.len() / 2;
                let coin = &self.0[mid_idx];
                match denom.cmp(&coin.denom.0) {
                    std::cmp::Ordering::Less => Vec::from(&self.0[..mid_idx])
                        .into_iter()
                        .find(|v| v.denom.0 == denom),
                    std::cmp::Ordering::Equal => Some(coin.clone()),
                    std::cmp::Ordering::Greater => Vec::from(&self.0[mid_idx + 1..])
                        .into_iter()
                        .find(|v| v.denom.0 == denom),
                }
            }
        }
    }

    // `get_denom_by_index` returns the Denom of the certain coin to make the findDup generic
    pub fn get_denom_by_index(&self, i: usize) -> String {
        self.0[i].denom.0.clone()
    }

    // `is_all_positive` returns true if there is at least one coin and all currencies
    // have a positive value.
    pub fn is_all_positive(&self) -> bool {
        if self.0.is_empty() {
            return false;
        }

        for coin in self.0.iter() {
            if !coin.amount.is_positive() {
                return false;
            }
        }

        true
    }
}

impl std::ops::Add for BaseCoins {
    type Output = BaseCoins;

    fn add(self, other: BaseCoins) -> Self::Output {
        self.safe_add(&other)
    }
}

impl std::fmt::Display for BaseCoins {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let coins: Vec<String> = self.0.iter().map(|c| c.to_string()).collect();
        write!(f, "{}", coins.join(","))
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
