pub mod error;
pub mod module;
pub mod types;

pub trait CosmosSdkContext {
    type AccAddress;
}
