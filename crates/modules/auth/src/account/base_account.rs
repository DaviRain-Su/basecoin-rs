use ibc_proto::cosmos::auth::v1beta1::BaseAccount as RawBaseAccount;
use ibc_proto::google::protobuf::Any;
use ibc_proto::protobuf::Protobuf;
use serde_derive::{Deserialize, Serialize};

pub const TYPE_URL: &str = "/cosmos.auth.v1beta1.BaseAccount";

#[derive(Clone, Deserialize, Serialize)]
pub struct BaseAccount {
    pub address: String,
    pub pub_key: Option<Any>,
    pub account_number: u64,
    pub sequence: u64,
}

impl ibc_proto::protobuf::Protobuf<RawBaseAccount> for BaseAccount {}

impl TryFrom<RawBaseAccount> for BaseAccount {
    type Error = String;

    fn try_from(account: RawBaseAccount) -> Result<Self, Self::Error> {
        Ok(BaseAccount {
            address: account
                .address
                .parse()
                .map_err(|_| "Failed to parse address".to_string())?,
            pub_key: account.pub_key,
            account_number: account.account_number,
            sequence: account.sequence,
        })
    }
}

impl From<BaseAccount> for RawBaseAccount {
    fn from(account: BaseAccount) -> Self {
        RawBaseAccount {
            address: account.address.to_string(),
            pub_key: account.pub_key,
            account_number: account.account_number,
            sequence: account.sequence,
        }
    }
}

impl From<BaseAccount> for Any {
    fn from(account: BaseAccount) -> Self {
        Any {
            type_url: TYPE_URL.to_string(),
            value: account.encode_vec(),
        }
    }
}
