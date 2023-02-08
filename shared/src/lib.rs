#![cfg_attr(not(feature = "std"), no_std)]

use concordium_std::{SchemaType, Address, Serialize};

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
