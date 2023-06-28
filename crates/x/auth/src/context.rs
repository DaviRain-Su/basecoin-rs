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

// AccountKeeperI is the interface contract that x/auth's keeper implements.
pub trait AccountKepperI: cosmos_x_module_api::CosmosSdkContext {
    type Account: AccountI;
    type PubKey: std::fmt::Display;
    type Error;

    /// Return a new account with the next account number and the specified address. Does not save the new account to the store.
    fn new_account_with_address(&mut self, address: Self::AccAddress) -> Self::Account;

    /// Return a new account with the next account number. Does not save the new account to the store.
    fn new_account(&mut self, account: Self::Account) -> Self::Account;

    /// Check if an account exists in the store.
    fn has_account(&self, address: Self::AccAddress) -> bool;

    /// Retrieve an account from the store.
    fn get_account(&self, address: Self::AccAddress) -> Option<Self::Account>;

    /// Set an account in the store.
    fn set_account(&mut self, account: Self::Account);

    /// Remove an account from the store.
    fn remove_account(&mut self, account: Self::Account);

    /// Iterate over all accounts, calling the provided function. Stop iteration when it returns true.
    fn iterate_accounts<F>(&self, f: F) -> Result<(), Self::Error>
    where
        F: FnMut(&Self::Account) -> bool;

    /// Fetch the public key of an account at a specified address
    fn get_pub_key(&self, address: Self::AccAddress) -> Result<Self::PubKey, Self::Error>;

    /// Fetch the sequence of an account at a specified address.
    fn get_sequence(&self, address: Self::AccAddress) -> Result<u64, Self::Error>;

    ///Fetch the next account number, and increment the internal counter.
    fn new_account_number(&mut self) -> Result<u64, Self::Error>;
}
