use crate::account::base_account::BaseAccount;
use ibc_proto::cosmos::auth::v1beta1::ModuleAccount as RawModuleAccount;
use ibc_proto::google::protobuf::Any;
use ibc_proto::protobuf::Protobuf;
use serde_derive::{Deserialize, Serialize};

pub const TYPE_URL: &str = "/cosmos.auth.v1beta1.ModuleAccount";

/// ModuleAccount defines an account for modules that holds coins on a pool.
#[derive(Serialize, Deserialize, Clone)]
pub struct ModuleAccount {
    pub base_account: Option<BaseAccount>,
    pub name: String,
    pub permissions: Vec<String>,
}

impl ibc_proto::protobuf::Protobuf<RawModuleAccount> for ModuleAccount {}

impl TryFrom<RawModuleAccount> for ModuleAccount {
    type Error = String;

    fn try_from(account: RawModuleAccount) -> Result<Self, Self::Error> {
        Ok(ModuleAccount {
            base_account: account.base_account.map(TryFrom::try_from).transpose()?,
            name: account.name,
            permissions: account.permissions,
        })
    }
}

impl From<ModuleAccount> for RawModuleAccount {
    fn from(account: ModuleAccount) -> Self {
        RawModuleAccount {
            base_account: account.base_account.map(Into::into),
            name: account.name,
            permissions: account.permissions,
        }
    }
}

impl From<ModuleAccount> for Any {
    fn from(account: ModuleAccount) -> Self {
        Any {
            type_url: TYPE_URL.to_string(),
            value: account.encode_vec(),
        }
    }
}
