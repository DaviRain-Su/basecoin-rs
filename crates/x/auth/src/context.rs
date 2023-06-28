/// AccountI is an interface used to store coins at a given address within state.
/// It presumes a notion of sequence numbers for replay protection,
/// a notion of account numbers for replay protection for previously pruned accounts,
/// and a pubkey for authentication purposes.
///
/// Many complex conditions can be used in the concrete struct which implements AccountI.
pub trait AccountI: std::fmt::Display {
    type Address;
    type PubKey;
    type Error;

    fn get_address(&self) -> &Self::Address;
    fn set_address(&mut self, address: Self::Address) -> Result<(), Self::Error>;

    fn get_pub_key(&self) -> &Self::PubKey;
    fn set_pub_key(&mut self, pubkey: Self::PubKey) -> Result<(), Self::Error>;

    fn get_account_number(&self) -> u64;
    fn set_account_number(&mut self, account_number: u64) -> Result<(), Self::Error>;

    fn get_sequence(&self) -> u64;
    fn set_sequence(&mut self, sequence: u64) -> Result<(), Self::Error>;
}

pub trait Account {
    /// Account address type
    type Address;
    /// Account public key type
    type PubKey;

    /// Returns the account's address.
    fn address(&self) -> &Self::Address;

    /// Returns the account's public key.
    fn pub_key(&self) -> &Self::PubKey;

    /// Returns the account's sequence. (used for replay protection)
    fn sequence(&self) -> u64;
}

pub trait AccountReader {
    type Error;
    type Address;
    type Account: Account;

    fn get_account(&self, address: Self::Address) -> Result<Self::Account, Self::Error>;
}

pub trait AccountKeeper {
    type Error;
    type Account: Account;

    fn set_account(&mut self, account: Self::Account) -> Result<(), Self::Error>;

    fn remove_account(&mut self, account: Self::Account) -> Result<(), Self::Error>;
}
