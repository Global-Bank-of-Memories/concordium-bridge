#![cfg_attr(not(feature = "std"), no_std)]

use std::collections::BTreeMap;
use concordium_cis2::{CIS0_STANDARD_IDENTIFIER, StandardIdentifier, StandardIdentifierOwned, SupportResult, SupportsQueryParams, SupportsQueryResponse, TokenIdUnit};
use concordium_std::{*};
use concordium_std::schema::Type::ByteArray;

use wgbm_shared::{MintParams, BurnParams};

/// Tag for the NewAdmin event.
pub const NEW_ADMIN_EVENT_TAG: u8 = 0;
pub const DEPOSIT_EVENT_TAG: u8 = 1;
pub const WITHDRAW_EVENT_TAG: u8 = 2;
pub const ADD_VALIDATOR_EVENT_TAG: u8 = 4;
pub const REMOVE_VALIDATOR_EVENT_TAG: u8 = 5;
pub const SET_REQUIRED_VALIDATORS_EVENT_TAG: u8 = 6;

/// List of supported standards by this contract address.
const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 1] =
    [CIS0_STANDARD_IDENTIFIER];

// Types

/// Contract token ID type.
/// Since this contract will only ever contain this one token type, we use the
/// smallest possible token ID.
type ContractTokenId = TokenIdUnit;

/// The contract state,
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S: HasStateApi> {
    /// The admin address can upgrade the contract, pause and unpause the
    /// contract, transfer the admin address to a new address, set
    /// implementors, and update the metadata URL in the contract.
    admin: Address,
    /// The token address bridge can mint tokens after signature validation
    token: ContractAddress,
    /// The token id bridge address can mint tokens after signature validation
    token_id: ContractTokenId,
    /// Contract is paused if `paused = true` and unpaused if `paused = false`.
    paused: bool,
    // Validators addresses legit to sing withdraw or refund operations
    validators: Vec<[u8; 33]>,
    // Set of executed request ids
    executed_requests: StateSet<[u8; 32], S>,
    // Number of validators required to sign withdrawal request
    validators_required: u8,
    // Validators Set version
    version: u32,
    /// Map with contract addresses providing implementations of additional
    /// standards.
    implementors: StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
}

/// The parameter type for the contract initialization`.
#[derive(Serialize, SchemaType)]
struct InitParams {
    token: ContractAddress,
    token_id: ContractTokenId,
    validators: Vec<[u8; 33]>,
    validators_required: u8,
}

/// The parameter type for the contract function `unwrap`.
/// Takes an amount of tokens and unwraps the CCD and sends it to a receiver.
#[derive(Serialize, SchemaType)]
struct DepositParams {
    destination: [u8; 256],
    amount: u64,
}

/// The parameter type for the contract function `wrap`.
/// It includes a receiver for receiving the wrapped CCD tokens.
#[derive(Serialize, SchemaType)]
struct WithdrawParams {
    // the id of the transfer
    id: [u8; 32],
    // unix timestamp of when the transaction should expire
    expiration: u64,
    // address who will receive the wGBM tokens
    to: Address,
    // the amount of tokens to be transferred
    amount: u64,
    // signatures of validators
    signatures: Vec<[u8; 64]>,
    // signature indexes of validators
    indexes: Vec<u8>,
}

/// The parameter type for the contract function `setImplementors`.
/// Takes a standard identifier and list of contract addresses providing
/// implementations of this standard.
#[derive(Debug, Serialize, SchemaType)]
struct SetRequiredValidatorsParams {
    /// The identifier for the standard.
    validators_required: u8,
}

/// The parameter type for the contract function `setImplementors`.
/// Takes a standard identifier and list of contract addresses providing
/// implementations of this standard.
#[derive(Debug, Serialize, SchemaType)]
struct AddValidatorParams {
    /// The identifier for the standard.
    validator: [u8; 33],
}

/// The parameter type for the contract function `setImplementors`.
/// Takes a standard identifier and list of contract addresses providing
/// implementations of this standard.
#[derive(Debug, Serialize, SchemaType)]
struct RemoveValidatorParams {
    /// The identifier for the standard.
    validator: [u8; 33],
}

/// The parameter type for the contract function `setImplementors`.
/// Takes a standard identifier and list of contract addresses providing
/// implementations of this standard.
#[derive(Debug, Serialize, SchemaType)]
struct SetImplementorsParams {
    /// The identifier for the standard.
    id: StandardIdentifierOwned,
    /// The addresses of the implementors of the standard.
    implementors: Vec<ContractAddress>,
}

/// The parameter type for the contract function `upgrade`.
/// Takes the new module and optionally an entrypoint to call in the new module
/// after triggering the upgrade. The upgrade is reverted if the entrypoint
/// fails. This is useful for doing migration in the same transaction triggering
/// the upgrade.
#[derive(Debug, Serialize, SchemaType)]
struct UpgradeParams {
    /// The new module reference.
    module: ModuleReference,
    /// Optional entrypoint to call in the new module after upgrade.
    migrate: Option<(OwnedEntrypointName, OwnedParameter)>,
}

/// The return type for the contract function `view`.
#[derive(Serialize, SchemaType)]
struct ReturnBasicState {
    /// The admin address can upgrade the contract, pause and unpause the
    /// contract, transfer the admin address to a new address, set
    /// implementors, and update the metadata URL in the contract.
    admin: Address,
    /// The token address
    token: ContractAddress,
    /// The token id
    token_id: ContractTokenId,
    /// Contract is paused if `paused = true` and unpaused if `paused = false`.
    paused: bool,
    /// List of validators public keys
    validators: Vec<[u8; 33]>,
    /// Minimum number of validators should sign withdrawal operation
    validators_required: u8,
    // Validators set version
    version: u32,
}

#[derive(Serialize, SchemaType)]
struct ReturnWithdrawHash {
    /// Generated hash for withdraw
    hash: [u8; 32],
}


/// The parameter type for the contract function `setPaused`.
#[derive(Serialize, SchemaType)]
#[repr(transparent)]
struct SetPausedParams {
    /// Contract is paused if `paused = true` and unpaused if `paused = false`.
    paused: bool,
}

/// A NewAdminEvent introduced by this smart contract.
#[derive(Serial, SchemaType)]
#[repr(transparent)]
struct NewAdminEvent {
    /// New admin address.
    new_admin: Address,
}

/// A NewAdminEvent introduced by this smart contract.
#[derive(Serial, SchemaType, Clone)]
struct DepositEvent {
    sender: Address,
    destination: [u8; 256],
    amount: u64,
}

/// A NewAdminEvent introduced by this smart contract.
#[derive(Serial, SchemaType, Clone)]
struct WithdrawEvent {
    id: [u8; 32],
    to: Address,
    amount: u64,
}

/// A AddedValidatorEvent introduced by this smart contract.
#[derive(Serial, SchemaType, Clone)]
struct AddedValidatorEvent {
    validator: [u8; 33],
    version: u32,
}

/// A RemovedValidatorEvent introduced by this smart contract.
#[derive(Serial, SchemaType, Clone)]
struct RemovedValidatorEvent {
    validator: [u8; 33],
    version: u32,
}

/// A SetRequiredValidators introduced by this smart contract.
#[derive(Serial, SchemaType)]
#[repr(transparent)]
struct SetRequiredValidatorsEvent {
    validators_required: u8,
}

/// Tagged events to be serialized for the event log.
enum BridgeEvent {
    NewAdmin(NewAdminEvent),
    Deposit(DepositEvent),
    Withdraw(WithdrawEvent),
    AddedValidator(AddedValidatorEvent),
    RemovedValidator(RemovedValidatorEvent),
    SetRequiredValidators(SetRequiredValidatorsEvent),
}

impl Serial for BridgeEvent {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        match self {
            BridgeEvent::NewAdmin(event) => {
                out.write_u8(NEW_ADMIN_EVENT_TAG)?;
                event.serial(out)
            }
            BridgeEvent::Deposit(event) => {
                out.write_u8(DEPOSIT_EVENT_TAG)?;
                event.serial(out)
            }
            BridgeEvent::Withdraw(event) => {
                out.write_u8(WITHDRAW_EVENT_TAG)?;
                event.serial(out)
            }
            BridgeEvent::AddedValidator(event) => {
                out.write_u8(ADD_VALIDATOR_EVENT_TAG)?;
                event.serial(out)
            }
            BridgeEvent::RemovedValidator(event) => {
                out.write_u8(REMOVE_VALIDATOR_EVENT_TAG)?;
                event.serial(out)
            }
            BridgeEvent::SetRequiredValidators(event) => {
                out.write_u8(SET_REQUIRED_VALIDATORS_EVENT_TAG)?;
                event.serial(out)
            }
        }
    }
}

/// Manual implementation of the `BridgeEventSchema` which includes both the
/// events specified in this contract and the events specified in the CIS-2
/// library. The events are tagged to distinguish them on-chain.
impl schema::SchemaType for BridgeEvent {
    fn get_type() -> schema::Type {
        let mut event_map = BTreeMap::new();
        event_map.insert(
            NEW_ADMIN_EVENT_TAG,
            (
                "NewAdmin".to_string(),
                schema::Fields::Named(vec![(String::from("new_admin"), Address::get_type())]),
            ),
        );
        event_map.insert(
            DEPOSIT_EVENT_TAG,
            (
                "Deposit".to_string(),
                schema::Fields::Named(vec![
                    (String::from("sender"), Address::get_type()),
                    (String::from("destination"), ByteArray(32)),
                    (String::from("amount"), u64::get_type()),
                ]),
            ),
        );
        event_map.insert(
            WITHDRAW_EVENT_TAG,
            (
                "Withdraw".to_string(),
                schema::Fields::Named(vec![
                    (String::from("id"), ByteArray(32)),
                    (String::from("recipient"), Address::get_type()),
                    (String::from("amount"), u64::get_type()),
                ]),
            ),
        );
        event_map.insert(
            ADD_VALIDATOR_EVENT_TAG,
            (
                "AddValidator".to_string(),
                schema::Fields::Named(vec![
                    (String::from("validator"), ByteArray(32)),
                    (String::from("version"), u32::get_type()),
                ]),
            ),
        );
        event_map.insert(
            REMOVE_VALIDATOR_EVENT_TAG,
            (
                "RemoveValidator".to_string(),
                schema::Fields::Named(vec![
                    (String::from("validator"), ByteArray(32)),
                    (String::from("version"), u32::get_type()),
                ]),
            ),
        );
        event_map.insert(
            SET_REQUIRED_VALIDATORS_EVENT_TAG,
            (
                "SetRequiredValidators".to_string(),
                schema::Fields::Named(vec![
                    (String::from("validators_required"), u8::get_type()),
                ]),
            ),
        );

        schema::Type::TaggedEnum(event_map)
    }
}

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
enum ContractError {
    Unauthorized,
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed logging: Log is full.
    LogFull,
    /// Failed logging: Log is malformed.
    LogMalformed,
    /// Contract is paused.
    ContractPaused,
    /// Failed to invoke a contract.
    InvokeContractError,
    /// Failed to invoke a transfer.
    InvokeTransferError,
    /// Upgrade failed because the new module does not exist.
    FailedUpgradeMissingModule,
    /// Upgrade failed because the new module does not contain a contract with a
    /// matching name.
    FailedUpgradeMissingContract,
    /// Upgrade failed because the smart contract version of the module is not
    /// supported.
    FailedUpgradeUnsupportedModuleVersion,
    /// Invalid number of required validators to sign operation.
    InvalidCountOFValidatorsRequired,
    /// Signed Withdrawal is already executed
    DuplicateWithdrawRequested,
    // Withdrawal amount is zero
    WithdrawAmountIsZero,
    /// Signed Withdrawal operation is expired.
    WithdrawalIsExpired,
    /// Signed Withdrawal operation refers to invalid validator index
    InvalidValidatorIndex,
    /// Duplicate validator index supplied to Withdrawal operation
    DuplicateValidatorIndex,
    /// Number of Signatures & Validator Indexes are not same
    InvalidNumberOfSignaturesAndIndexes,
    /// Number of supplied signatures is less than required minimum number of signatures
    IncorrectNumberOfSignaturesSupplied,
    /// Validator signature is invalid
    InvalidSignature,
    /// Requested deposit amount is zero
    DepositAmountIsZero,
}

type ContractResult<A> = Result<A, ContractError>;

/// Mapping the logging errors to ContractError.
impl From<LogError> for ContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

/// Mapping errors related to contract invocations to ContractError.
impl<T> From<CallContractError<T>> for ContractError {
    fn from(_cce: CallContractError<T>) -> Self { Self::InvokeContractError }
}

/// Mapping errors related to contract upgrades to ContractError.
impl From<UpgradeError> for ContractError {
    #[inline(always)]
    fn from(ue: UpgradeError) -> Self {
        match ue {
            UpgradeError::MissingModule => Self::FailedUpgradeMissingModule,
            UpgradeError::MissingContract => Self::FailedUpgradeMissingContract,
            UpgradeError::UnsupportedModuleVersion => Self::FailedUpgradeUnsupportedModuleVersion,
        }
    }
}

impl<S: HasStateApi> State<S> {
    /// Creates a new state with no one owning any tokens by default.
    fn new(
        state_builder: &mut StateBuilder<S>,
        admin: Address,
        token: ContractAddress,
        token_id: ContractTokenId,
        validators: Vec<[u8; 33]>,
        validators_required: u8,
    ) -> Self {
        State {
            admin,
            token,
            token_id,
            paused: false,
            validators,
            executed_requests: state_builder.new_set(),
            validators_required,
            version: 0,
            implementors: state_builder.new_map(),
        }
    }

    /// Checks if request is executed
    fn is_executed_withdrawal_request(&self, id: &[u8; 32]) -> bool {
        self.executed_requests.contains(id)
    }

    fn add_withdrawal_request(&mut self, id: [u8; 32]) {
        self.executed_requests.insert(id);
    }

    /// Update the state adding a new operator for a given token id and address.
    /// Succeeds even if the `operator` is already an operator for this
    /// `token_id` and `address`.
    fn add_validator(
        &mut self,
        validator: [u8; 33],
    ) {
        if ! self.validators.contains(&validator) {
            self.validators.push(validator);
            self.version += 1;
        }
    }

    /// Update the state removing an operator for a given token id and address.
    /// Succeeds even if the `operator` is not an operator for this `token_id`
    /// and `address`.
    fn remove_validator(&mut self, validator: &[u8; 33]) {
        for i in 0..self.validators.len() {
            if self.validators[i].eq(validator) {
                self.validators.remove(i);
                self.version += 1;
                break;
            }
        }
    }

    /// Check if state contains any implementors for a given standard.
    fn have_implementors(&self, std_id: &StandardIdentifierOwned) -> SupportResult {
        if let Some(addresses) = self.implementors.get(std_id) {
            SupportResult::SupportBy(addresses.to_vec())
        } else {
            SupportResult::NoSupport
        }
    }

    /// Set implementors for a given standard.
    fn set_implementors(
        &mut self,
        std_id: StandardIdentifierOwned,
        implementors: Vec<ContractAddress>,
    ) {
        self.implementors.insert(std_id, implementors);
    }

    fn withdraw_hash(
        &self,
        id: [u8; 32],
        address: Address,
        amount: u64,
        expiration: u64,
        crypto_primitives: &impl HasCryptoPrimitives
    ) -> HashKeccak256 {
        let mut message: Vec<u8> = vec![];

        message.extend(self.version.to_le_bytes());
        message.extend(id);

        match address {
            Address::Account(address) => {
                message.extend([1u8; 1]);
                message.extend(address.0);
            },
            Address::Contract(contract) => {
                message.extend([2u8; 1]);
                message.extend(contract.index.to_le_bytes());
                message.extend(contract.subindex.to_le_bytes());
            }
        }

        message.extend(amount.to_le_bytes());
        message.extend(expiration.to_le_bytes());

        crypto_primitives.hash_keccak_256(message.as_slice())
    }
}

// Contract functions

/// Initialize contract instance with no initial tokens.
/// Logs a `Mint` event for the single token id with no amounts.
/// Logs a `TokenMetadata` event with the metadata url and hash.
/// Logs a `NewAdmin` event with the invoker as admin.
#[init(
contract = "gbm_Bridge",
enable_logger,
parameter = "InitParams",
event = "BridgeEvent"
)]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
    logger: &mut impl HasLogger,
) -> InitResult<State<S>> {
    // Parse the parameter.
    let params: InitParams = ctx.parameter_cursor().get()?;
    // Get the instantiator of this contract instance to be used as the initial
    // admin.
    let invoker = Address::Account(ctx.init_origin());

    let token_address = params.token;
    let token_id = params.token_id;
    let validators = params.validators;
    let validators_required = params.validators_required;

    // Construct the initial contract state.
    let state = State::new(state_builder, invoker, token_address, token_id, validators, validators_required);

    // Log event for the new admin.
    logger.log(&BridgeEvent::NewAdmin(NewAdminEvent {
        new_admin: invoker,
    }))?;

    Ok(state)
}

/// Function to view the basic state of the contract.
#[receive(
contract = "gbm_Bridge",
name = "withdraw_hash",
parameter = "WithdrawParams",
return_value = "ReturnWithdrawHash",
error = "ContractError",
crypto_primitives
)]
fn contract_withdraw_hash<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType=S>,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<ReturnWithdrawHash> {
    // Parse the parameter.
    let params: WithdrawParams = ctx.parameter_cursor().get()?;

    let hash = host.state().withdraw_hash(
        params.id,
        params.to,
        params.amount,
        params.expiration,
        crypto_primitives,
    );

    Ok(
        ReturnWithdrawHash {
            hash: hash.0
        }
    )
}


/// Wrap an amount of CCD into wGBM tokens and transfer the tokens if the sender
/// is not the receiver.
#[receive(
contract = "gbm_Bridge",
name = "withdraw",
parameter = "WithdrawParams",
error = "ContractError",
crypto_primitives,
mutable,
enable_logger,
)]
fn contract_withdraw<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType=S>,
    logger: &mut impl HasLogger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<()>
{
    // Check that contract is not paused.
    ensure!(!host.state().paused, ContractError::ContractPaused);

    // Parse the parameter.
    let params: WithdrawParams = ctx.parameter_cursor().get()?;

    ensure!(params.amount > 0, ContractError::WithdrawAmountIsZero);
    ensure!(params.expiration > ctx.metadata().slot_time().timestamp_millis(), ContractError::WithdrawalIsExpired);
    ensure!(params.signatures.len() == params.indexes.len(), ContractError::InvalidNumberOfSignaturesAndIndexes);
    ensure!(params.signatures.len() >= host.state().validators_required.into(), ContractError::IncorrectNumberOfSignaturesSupplied);

    ensure!(!host.state().is_executed_withdrawal_request(&params.id), ContractError::DuplicateWithdrawRequested);

    let hash = host.state().withdraw_hash(
        params.id,
        params.to,
        params.amount,
        params.expiration,
        crypto_primitives,
    );

    let mut processed_validators: Vec<u8> = vec![];

    for i in 0..params.indexes.len() {
        let validator_index = params.indexes[i].into();
        let signature = params.signatures[i];

        if processed_validators.contains(&validator_index) {
            bail!(ContractError::DuplicateValidatorIndex);
        }

        if let Some(public_key) = host.state().validators.get(validator_index as usize) {
            let is_correct = crypto_primitives.verify_ecdsa_secp256k1_signature(
                PublicKeyEcdsaSecp256k1(public_key.clone()),
                SignatureEcdsaSecp256k1(signature),
                hash.0,
            );

            if is_correct {
                processed_validators.push(validator_index);
            } else {
                bail!(ContractError::InvalidSignature);
            }
        } else {
            bail!(ContractError::InvalidValidatorIndex);
        }
    }

    host.state_mut().add_withdrawal_request(params.id);

    let token = host.state().token.clone();

    let mint_parameter = MintParams {
        to: params.to,
        amount: params.amount,
    };

    // Let Token contract to mint tokens.
    host.invoke_contract(
        &token,
        &mint_parameter,
        EntrypointName::new_unchecked("mint"),
        Amount::zero(),
    )?;

    // Log withdrawal.
    logger.log(&BridgeEvent::Withdraw(WithdrawEvent {
        id: params.id,
        to: params.to,
        amount: params.amount,
    }))?;

    Ok(())
}

/// Unwrap an amount of wGBM tokens into CCD
#[receive(
contract = "gbm_Bridge",
name = "deposit",
parameter = "DepositParams",
error = "ContractError",
enable_logger,
mutable
)]
fn contract_deposit<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType=S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()>
{
    // Check that contract is not paused.
    ensure!(!host.state().paused, ContractError::ContractPaused);

    // Parse the parameter.
    let params: DepositParams = ctx.parameter_cursor().get()?;

    ensure!(params.amount > 0, ContractError::DepositAmountIsZero);

    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    let token = host.state().token.clone();

    let burn_parameter = BurnParams {
        from: sender,
        amount: params.amount,
    };

    // Let Token contract to burn tokens.
    host.invoke_contract(
        &token,
        &burn_parameter,
        EntrypointName::new_unchecked("burn"),
        Amount::zero(),
    )?;

    // Log the deposit of tokens.
    logger.log(&BridgeEvent::Deposit(DepositEvent {
        sender,
        destination: params.destination,
        amount: params.amount,
    }))?;

    Ok(())
}

/// Add validator.
///
/// It rejects if:
/// - Sender is not the current admin of the contract instance.
/// - It fails to parse the parameter.
#[receive(
contract = "gbm_Bridge",
name = "addValidator",
parameter = "[u8; 33]",
error = "ContractError",
enable_logger,
mutable
)]
fn contract_add_validator<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType=S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()>
{
    // Check that only the current admin is authorized to update the admin address.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    // Parse the parameter.
    let validator: [u8; 33] = ctx.parameter_cursor().get()?;

    // Update the admin variable.
    let state = host.state_mut();
    state.add_validator(validator);

    // Log a new admin event.
    logger.log(&BridgeEvent::AddedValidator(AddedValidatorEvent {
        validator,
        version: state.version
    }))?;

    Ok(())
}

/// Remove validator.
///
/// It rejects if:
/// - Sender is not the current admin of the contract instance.
/// - It fails to parse the parameter.
#[receive(
contract = "gbm_Bridge",
name = "removeValidator",
parameter = "[u8; 33]",
error = "ContractError",
enable_logger,
mutable
)]
fn contract_remove_validator<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType=S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()>
{
    // Check that only the current admin is authorized to update the admin address.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    // Parse the parameter.
    let validator: [u8; 33] = ctx.parameter_cursor().get()?;

    // Update the admin variable.
    let state = host.state_mut();
    state.remove_validator(&validator);

    // Log a new admin event.
    logger.log(&BridgeEvent::RemovedValidator(RemovedValidatorEvent {
        validator,
        version: state.version
    }))?;

    Ok(())
}

/// Set required validators amount to sign withdraw operation.
///
/// It rejects if:
/// - Sender is not the current admin of the contract instance.
/// - It fails to parse the parameter.
#[receive(
contract = "gbm_Bridge",
name = "setValidatorsRequired",
parameter = "u32",
error = "ContractError",
enable_logger,
mutable
)]
fn contract_set_validators_required<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType=S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()>
{
    // Check that only the current admin is authorized to update the admin address.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    // Parse the parameter.
    let validators_required: u8 = ctx.parameter_cursor().get()?;

    // Update the admin variable.
    let state = host.state_mut();

    if state.validators_required as usize > state.validators.len() {
        bail!(ContractError::InvalidCountOFValidatorsRequired);
    }

    state.validators_required = validators_required;

    // Log a new admin event.
    logger.log(&BridgeEvent::SetRequiredValidators(SetRequiredValidatorsEvent {
        validators_required
    }))?;

    Ok(())
}


/// Transfer the admin address to a new admin address.
///
/// It rejects if:
/// - Sender is not the current admin of the contract instance.
/// - It fails to parse the parameter.
#[receive(
contract = "gbm_Bridge",
name = "updateAdmin",
parameter = "Address",
error = "ContractError",
enable_logger,
mutable
)]
fn contract_update_admin<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType=S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()>
{
    // Check that only the current admin is authorized to update the admin address.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    // Parse the parameter.
    let new_admin = ctx.parameter_cursor().get()?;

    // Update the admin variable.
    host.state_mut().admin = new_admin;

    // Log a new admin event.
    logger.log(&BridgeEvent::NewAdmin(NewAdminEvent {
        new_admin,
    }))?;

    Ok(())
}

/// Pause/Unpause this smart contract instance by the admin. All non-admin
/// state-mutative functions (wrap, unwrap, transfer, updateOperator) cannot be
/// executed when the contract is paused.
///
/// It rejects if:
/// - Sender is not the admin of the contract instance.
/// - It fails to parse the parameter.
#[receive(
contract = "gbm_Bridge",
name = "setPaused",
parameter = "SetPausedParams",
error = "ContractError",
mutable
)]
fn contract_set_paused<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType=S>,
) -> ContractResult<()>
{
    // Check that only the admin is authorized to pause/unpause the contract.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    // Parse the parameter.
    let params: SetPausedParams = ctx.parameter_cursor().get()?;

    // Update the paused variable.
    host.state_mut().paused = params.paused;

    Ok(())
}

/// Function to view the basic state of the contract.
#[receive(
contract = "gbm_Bridge",
name = "view",
return_value = "ReturnBasicState",
error = "ContractError"
)]
fn contract_view<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType=S>,
) -> ContractResult<ReturnBasicState> {
    let state = host.state();

    Ok(
        ReturnBasicState {
            admin: state.admin,
            token: state.token,
            token_id: state.token_id,
            paused: state.paused,
            validators: state.validators.iter()
                .map(|validator| validator.clone()).collect(),
            validators_required: state.validators_required,
            version: state.version,
        }
    )
}

/// Get the supported standards or addresses for a implementation given list of
/// standard identifiers.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
contract = "gbm_Bridge",
name = "supports",
parameter = "SupportsQueryParams",
return_value = "SupportsQueryResponse",
error = "ContractError"
)]
fn contract_supports<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType=S>,
) -> ContractResult<SupportsQueryResponse> {
    // Parse the parameter.
    let params: SupportsQueryParams = ctx.parameter_cursor().get()?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for std_id in params.queries {
        if SUPPORTS_STANDARDS.contains(&std_id.as_standard_identifier()) {
            response.push(SupportResult::Support);
        } else {
            response.push(host.state().have_implementors(&std_id));
        }
    }
    let result = SupportsQueryResponse::from(response);
    Ok(result)
}

/// Set the addresses for an implementation given a standard identifier and a
/// list of contract addresses.
///
/// It rejects if:
/// - Sender is not the admin of the contract instance.
/// - It fails to parse the parameter.
#[receive(
contract = "gbm_Bridge",
name = "setImplementors",
parameter = "SetImplementorsParams",
error = "ContractError",
mutable
)]
fn contract_set_implementor<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType=S>,
) -> ContractResult<()> {
    // Check that only the admin is authorized to set implementors.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);
    // Parse the parameter.
    let params: SetImplementorsParams = ctx.parameter_cursor().get()?;
    // Update the implementors in the state
    host.state_mut().set_implementors(params.id, params.implementors);
    Ok(())
}

/// Upgrade this smart contract instance to a new module and call optionally a
/// migration function after the upgrade.
///
/// It rejects if:
/// - Sender is not the admin of the contract instance.
/// - It fails to parse the parameter.
/// - If the ugrade fails.
/// - If the migration invoke fails.
///
/// This function is marked as `low_level`. This is **necessary** since the
/// high-level mutable functions store the state of the contract at the end of
/// execution. This conflicts with migration since the shape of the state
/// **might** be changed by the migration function. If the state is then written
/// by this function it would overwrite the state stored by the migration
/// function.
#[receive(
contract = "gbm_Bridge",
name = "upgrade",
parameter = "UpgradeParams",
error = "ContractError",
low_level
)]
fn contract_upgrade<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<S>,
) -> ContractResult<()> {
    // Read the top-level contract state.
    let state: State<S> = host.state().read_root()?;

    // Check that only the admin is authorized to upgrade the smart contract.
    ensure_eq!(ctx.sender(), state.admin, ContractError::Unauthorized);
    // Parse the parameter.
    let params: UpgradeParams = ctx.parameter_cursor().get()?;
    // Trigger the upgrade.
    host.upgrade(params.module)?;
    // Call the migration function if provided.
    if let Some((func, parameters)) = params.migrate {
        host.invoke_contract_raw(
            &ctx.self_address(),
            parameters.as_parameter(),
            func.as_entrypoint_name(),
            Amount::zero(),
        )?;
    }
    Ok(())
}

// Tests

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;
    use secp256k1::{Secp256k1, Message, SecretKey, PublicKey};

    const ACCOUNT_0: AccountAddress = AccountAddress([0u8; 32]);
    const ADDRESS_0: Address = Address::Account(ACCOUNT_0);
    const ACCOUNT_1: AccountAddress = AccountAddress([1u8; 32]);
    const ADDRESS_1: Address = Address::Account(ACCOUNT_1);
    const TIME_NOW: u64 = 1675957007;

    const ADMIN_ACCOUNT: AccountAddress = AccountAddress([1u8; 32]);
    const ADMIN_ADDRESS: Address = Address::Account(ADMIN_ACCOUNT);
    const NEW_ADMIN_ACCOUNT: AccountAddress = AccountAddress([2u8; 32]);
    const NEW_ADMIN_ADDRESS: Address = Address::Account(NEW_ADMIN_ACCOUNT);
    const TOKEN_ID: ContractTokenId = TokenIdUnit();

    const VALIDATOR_PRV_KEY_0: [u8; 32] = [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef];
    const VALIDATOR_PUB_KEY_0: [u8; 33] = [0x03, 0x46, 0x46, 0xae, 0x50, 0x47, 0x31, 0x6b, 0x42, 0x30, 0xd0, 0x08, 0x6c, 0x8a, 0xce, 0xc6, 0x87, 0xf0, 0x0b, 0x1c, 0xd9, 0xd1, 0xdc, 0x63, 0x4f, 0x6c, 0xb3, 0x58, 0xac, 0x0a, 0x9a, 0x8f, 0xff];

    const _VALIDATOR_PRV_KEY_1: [u8; 32] = [0xd0, 0xe5, 0x15, 0x47, 0xae, 0x21, 0x7d, 0x09, 0xe3, 0x23, 0xa9, 0xba, 0xbb, 0xa1, 0x88, 0xff, 0x88, 0x70, 0xae, 0x1d, 0x62, 0x37, 0x87, 0xb2, 0x6e, 0x6e, 0x96, 0xd3, 0x89, 0x3c, 0x8c, 0x70];
    const VALIDATOR_PUB_KEY_1: [u8; 33] = [0x02, 0xe1, 0xcd, 0x9b, 0xcc, 0xcb, 0xec, 0x11, 0x30, 0x53, 0x19, 0xa7, 0x55, 0x61, 0x42, 0xa6, 0xf3, 0x0c, 0xb9, 0x30, 0x38, 0xc3, 0xcf, 0xdb, 0x3f, 0xe0, 0x39, 0xc1, 0x9a, 0x51, 0x70, 0x00, 0x68];

    /// Test helper function which creates a contract state where ADDRESS_0 owns
    /// 400 tokens.
    fn initial_state<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> State<S> {
        let state = State::new(
            state_builder,
            ADMIN_ADDRESS,
            ContractAddress::new(100, 100),
            TOKEN_ID,
            vec![VALIDATOR_PUB_KEY_0],
            1,
        );

        state
    }

    /// Test adding an operator succeeds and the appropriate event is logged.
    #[concordium_test]
    fn test_add_validator() {
        // Set up the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        let parameter = AddValidatorParams {
            validator: VALIDATOR_PUB_KEY_1
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Call the contract function.
        let result: ContractResult<()> = contract_add_validator(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_err(), "Results in success");

        let result = contract_view(&ctx, &host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        claim_eq!(result.as_ref().unwrap().validators.len(), 1, "Validators count is not equal 1");
        claim!(!result.unwrap().validators.contains(&VALIDATOR_PUB_KEY_1), "New validator added");

        ctx.set_sender(ADMIN_ADDRESS);

        // Call the contract function.
        let result: ContractResult<()> = contract_add_validator(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Call the contract function for duplicate validator.
        let result: ContractResult<()> = contract_add_validator(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        let result = contract_view(&ctx, &host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        claim_eq!(result.as_ref().unwrap().validators.len(), 2, "Validators count is not equal 2");
        claim_eq!(result.as_ref().unwrap().version, 1, "Version is not equal 1");
        claim!(result.unwrap().validators.contains(&VALIDATOR_PUB_KEY_1), "New validator is not added");
    }

    #[concordium_test]
    fn test_remove_validator() {
        // Set up the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        host.state_mut().validators.push(VALIDATOR_PUB_KEY_1);

        let parameter = RemoveValidatorParams {
            validator: VALIDATOR_PUB_KEY_1
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Call the contract function.
        let result: ContractResult<()> = contract_remove_validator(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_err(), "Results in success");

        let result = contract_view(&ctx, &host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        claim_eq!(result.as_ref().unwrap().validators.len(), 2, "Validators count is not equal 2");
        claim!(result.unwrap().validators.contains(&VALIDATOR_PUB_KEY_1), "Existent validator removed");

        ctx.set_sender(ADMIN_ADDRESS);

        // Call the contract function.
        let result: ContractResult<()> = contract_remove_validator(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        let result = contract_view(&ctx, &host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        claim_eq!(result.as_ref().unwrap().validators.len(), 1, "Validators count is not equal 1");
        claim_eq!(result.as_ref().unwrap().version, 1, "Version is not equal 1");
        claim!(!result.unwrap().validators.contains(&VALIDATOR_PUB_KEY_1), "Existent validator not removed");
    }

    #[concordium_test]
    fn test_set_min_validators_required() {
        // Set up the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        host.state_mut().validators.push(VALIDATOR_PUB_KEY_1);

        let parameter = SetRequiredValidatorsEvent {
            validators_required: 2
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Call the contract function.
        let result: ContractResult<()> = contract_set_validators_required(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_err(), "Results in success");

        let result = contract_view(&ctx, &host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        claim_eq!(result.unwrap().validators_required, 1, "Required validators count is not equal 1");

        ctx.set_sender(ADMIN_ADDRESS);

        // Call the contract function.
        let result: ContractResult<()> = contract_set_validators_required(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        let result = contract_view(&ctx, &host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        claim_eq!(result.unwrap().validators_required, 2, "Required validators count is not equal 2");
    }

    /// Test withdraw function.
    #[concordium_test]
    fn test_withdraw() {
        // Set up the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_1);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(TIME_NOW));

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // We are simulating reentrancy with this mock because we mutate the state.
        host.setup_mock_entrypoint(
            host.state().token.clone(),
            EntrypointName::new_unchecked("mint").into(),
            MockFn::new_v1(|_parameter, _amount, _balance, _state: &mut State<TestStateApi>| {
                Ok((true, ()))
            }),
        );

        let crypto_primitives = TestCryptoPrimitives::new();

        // Set up the parameter.
        let wrap_params = WithdrawParams {
            id: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
            expiration: TIME_NOW + 3600 * 8,
            to: ADDRESS_1,
            amount: 10000u64,
            signatures: vec![],
            indexes: vec![0],
        };
        let parameter_bytes = to_bytes(&wrap_params);
        ctx.set_parameter(&parameter_bytes);

        let result: ContractResult<()> =
            contract_withdraw(&ctx, &mut host, &mut logger, &crypto_primitives);

        // Check the result.
        claim_eq!(result.err().unwrap(), ContractError::InvalidNumberOfSignaturesAndIndexes, "Results in success");

        let wrap_params = WithdrawParams {
            id: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
            expiration: TIME_NOW + 3600 * 8,
            to: ADDRESS_1,
            amount: 10000u64,
            signatures: vec![[1u8; 64]],
            indexes: vec![],
        };
        let parameter_bytes = to_bytes(&wrap_params);
        ctx.set_parameter(&parameter_bytes);

        let result: ContractResult<()> =
            contract_withdraw(&ctx, &mut host, &mut logger, &crypto_primitives);

        // Check the result.
        claim_eq!(result.err().unwrap(), ContractError::InvalidNumberOfSignaturesAndIndexes, "Results in success");

        let wrap_params = WithdrawParams {
            id: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
            expiration: TIME_NOW - 3600 * 8,
            to: ADDRESS_1,
            amount: 0,
            signatures: vec![[1u8; 64]],
            indexes: vec![0],
        };
        let parameter_bytes = to_bytes(&wrap_params);
        ctx.set_parameter(&parameter_bytes);

        let result: ContractResult<()> =
            contract_withdraw(&ctx, &mut host, &mut logger, &crypto_primitives);

        // Check the result.
        claim_eq!(result.err().unwrap(), ContractError::WithdrawAmountIsZero, "Results in success");

        let wrap_params = WithdrawParams {
            id: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
            expiration: TIME_NOW - 3600 * 8,
            to: ADDRESS_1,
            amount: 10000,
            signatures: vec![[1u8; 64]],
            indexes: vec![0],
        };
        let parameter_bytes = to_bytes(&wrap_params);
        ctx.set_parameter(&parameter_bytes);

        let result: ContractResult<()> =
            contract_withdraw(&ctx, &mut host, &mut logger, &crypto_primitives);

        // Check the result.
        claim_eq!(result.err().unwrap(), ContractError::WithdrawalIsExpired, "Results in success");

        let wrap_params = WithdrawParams {
            id: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
            expiration: TIME_NOW + 3600 * 8,
            to: ADDRESS_1,
            amount: 10000,
            signatures: vec![[1u8; 64]],
            indexes: vec![0],
        };
        let parameter_bytes = to_bytes(&wrap_params);
        ctx.set_parameter(&parameter_bytes);

        let result: ContractResult<()> =
            contract_withdraw(&ctx, &mut host, &mut logger, &crypto_primitives);

        // Check the result.
        claim_eq!(result.err().unwrap(), ContractError::InvalidSignature, "Results in success");

        let mut wrap_params = WithdrawParams {
            id: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
            expiration: TIME_NOW + 3600 * 8,
            to: ADDRESS_1,
            amount: 10000,
            signatures: vec![[1u8; 64]],
            indexes: vec![0],
        };
        let parameter_bytes = to_bytes(&wrap_params);
        ctx.set_parameter(&parameter_bytes);

        let result: ContractResult<ReturnWithdrawHash> =
            contract_withdraw_hash(&ctx, &host, &crypto_primitives);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");
        let hash = result.unwrap().hash;

        let secp = Secp256k1::new();
        let secret_key = SecretKey::from_slice(&VALIDATOR_PRV_KEY_0).expect("32 bytes, within curve order");
        let public_key = PublicKey::from_secret_key(&secp, &secret_key);

        claim_eq!(public_key.serialize(), VALIDATOR_PUB_KEY_0, "Validator 0 public key is not correctly set");

        let message = Message::from_slice(&hash).expect("32 bytes");

        let sig = secp.sign_ecdsa(&message, &secret_key);
        claim!(secp.verify_ecdsa(&message, &sig, &public_key).is_ok(), "Pre-check ecdsa verification failed");

        wrap_params.signatures = vec![sig.serialize_compact()];

        let parameter_bytes = to_bytes(&wrap_params);
        ctx.set_parameter(&parameter_bytes);

        let result: ContractResult<()> =
            contract_withdraw(&ctx, &mut host, &mut logger, &crypto_primitives);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&BridgeEvent::Withdraw(WithdrawEvent {
                id: wrap_params.id,
                to: wrap_params.to,
                amount: wrap_params.amount,
            })),
            "Incorrect event emitted"
        );

        let result: ContractResult<()> =
            contract_withdraw(&ctx, &mut host, &mut logger, &crypto_primitives);

        // Check the result.
        claim_eq!(result.err().unwrap(), ContractError::DuplicateWithdrawRequested, "Results in rejection");
    }

    /// Test deposit function.
    #[concordium_test]
    fn test_deposit() {
        // Set up the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_1);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // We are simulating reentrancy with this mock because we mutate the state.
        host.setup_mock_entrypoint(
            host.state().token.clone(),
            EntrypointName::new_unchecked("burn").into(),
            MockFn::new_v1(|parameter, _amount, _balance, _state: &mut State<TestStateApi>| {
                let params: BurnParams = match from_bytes(parameter.0) {
                    Ok(params) => params,
                    Err(_) => return Err(CallContractError::Trap),
                };

                if params.from == ADDRESS_1 {
                    Err(CallContractError::Trap)
                } else {
                    Ok((true, ()))
                }
            }),
        );

        // Set up the parameter.
        let deposit_params = DepositParams {
            destination: [10u8; 32],
            amount: 10000u64,
        };

        let parameter_bytes = to_bytes(&deposit_params);
        ctx.set_parameter(&parameter_bytes);

        let result: ContractResult<()> =
            contract_deposit(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_err(), "Results in success");

        ctx.set_sender(ADDRESS_0);

        let result: ContractResult<()> =
            contract_deposit(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&BridgeEvent::Deposit(DepositEvent {
                sender: ADDRESS_0,
                destination: deposit_params.destination,
                amount: deposit_params.amount,
            })),
            "Incorrect event emitted"
        );
    }

    /// Test admin can update to a new admin address.
    #[concordium_test]
    fn test_update_admin() {
        // Set up the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);
        let mut logger = TestLogger::init();

        // Set up the parameter.
        let parameter_bytes = to_bytes(&[NEW_ADMIN_ADDRESS]);
        ctx.set_parameter(&parameter_bytes);

        // Set up the state and host.
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be the old admin address");

        // Call the contract function.
        let result: ContractResult<()> = contract_update_admin(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the admin state.
        claim_eq!(host.state().admin, NEW_ADMIN_ADDRESS, "Admin should be the new admin address");

        // Check the logs
        claim_eq!(logger.logs.len(), 1, "Exactly one event should be logged");

        // Check the event
        claim!(
            logger.logs.contains(&to_bytes(&BridgeEvent::NewAdmin(NewAdminEvent {
                new_admin: NEW_ADMIN_ADDRESS,
            }))),
            "Missing event for the new admin"
        );
    }

    /// Test that only the current admin can update the admin address.
    #[concordium_test]
    fn test_update_admin_not_authorized() {
        // Set up the context.
        let mut ctx = TestReceiveContext::empty();
        // NEW_ADMIN is not the current admin but tries to update the admin variable to
        // its own address.
        ctx.set_sender(NEW_ADMIN_ADDRESS);
        let mut logger = TestLogger::init();

        // Set up the parameter.
        let parameter_bytes = to_bytes(&[NEW_ADMIN_ADDRESS]);
        ctx.set_parameter(&parameter_bytes);

        // Set up the state and host.
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be the old admin address");

        // Call the contract function.
        let result: ContractResult<()> = contract_update_admin(&ctx, &mut host, &mut logger);

        // Check that invoke failed.
        claim_eq!(
            result,
            Err(ContractError::Unauthorized),
            "Update admin should fail because not the current admin tries to update"
        );

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be still the old admin address");
    }

    /// Test pausing the contract.
    #[concordium_test]
    fn test_pause() {
        // Set up the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        // Set up the parameter to pause the contract.
        let parameter_bytes = to_bytes(&true);
        ctx.set_parameter(&parameter_bytes);

        // Set up the state and host.
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> = contract_set_paused(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check contract is paused.
        claim_eq!(host.state().paused, true, "Smart contract should be paused");
    }

    /// Test unpausing the contract.
    #[concordium_test]
    fn test_unpause() {
        // Set up the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        // Set up the parameter to pause the contract.
        let parameter_bytes = to_bytes(&true);
        ctx.set_parameter(&parameter_bytes);

        // Set up the state and host.
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> = contract_set_paused(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check contract is paused.
        claim_eq!(host.state().paused, true, "Smart contract should be paused");

        // Set up the parameter to unpause the contract.
        let parameter_bytes = to_bytes(&false);
        ctx.set_parameter(&parameter_bytes);

        // Call the contract function.
        let result: ContractResult<()> = contract_set_paused(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check contract is unpaused.
        claim_eq!(host.state().paused, false, "Smart contract should be unpaused");
    }

    /// Test that only the current admin can pause/unpause the contract.
    #[concordium_test]
    fn test_pause_not_authorized() {
        // Set up the context.
        let mut ctx = TestReceiveContext::empty();
        // NEW_ADMIN is not the current admin but tries to pause/unpause the contract.
        ctx.set_sender(NEW_ADMIN_ADDRESS);

        // Set up the parameter to pause the contract.
        let parameter_bytes = to_bytes(&true);
        ctx.set_parameter(&parameter_bytes);

        // Set up the state and host.
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> = contract_set_paused(&ctx, &mut host);

        // Check that invoke failed.
        claim_eq!(
            result,
            Err(ContractError::Unauthorized),
            "Pause should fail because not the current admin tries to invoke it"
        );
    }
}

