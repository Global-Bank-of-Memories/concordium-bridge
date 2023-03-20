#![cfg_attr(not(feature = "std"), no_std)]

use concordium_std::{SchemaType, Address, Serialize};
use concordium_cis2::{TransferParams, OnReceivingCis2Params, TokenIdUnit, TokenAmountU64};

/// Contract token ID type.
/// Since this contract will only ever contain this one token type, we use the
/// smallest possible token ID.
pub type ContractTokenId = TokenIdUnit;

/// Contract token amount type.
pub type ContractTokenAmount = TokenAmountU64;

// Contract functions required by the CIS-2 standard
pub type TransferParameter = TransferParams<ContractTokenId, ContractTokenAmount>;

pub type OnReceivingCis2Parameter = OnReceivingCis2Params<ContractTokenId, ContractTokenAmount>;

/// The parameter type for the contract function `mint`.
#[derive(Serialize, SchemaType)]
pub struct MintParams {
    /// The address to receive these tokens.
    /// If the receiver is the sender of the message minting the tokens, it
    /// will not log a transfer event.
    pub to: Address,
    /// The amount of tokens to mint.
    pub amount: u64,

}

/// The parameter type for the contract function `burn`.
#[derive(Serialize, SchemaType)]
pub struct BurnParams {
    /// The owner of the tokens.
    pub from: Address,
    /// The amount of tokens to burn.
    pub amount: u64,
}
