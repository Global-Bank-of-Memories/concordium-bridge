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
    destination: [u8; 32],
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
    destination: [u8; 32],
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
    WithdrawalIsAlreadyExecuted,
    /// Signed Withdrawal operation is not valid anymore.
    WithdrawalIsExpired,
    /// Signed Withdrawal operation refers to invalid validator index
    InvalidValidatorIndex,
    /// Duplicate validator index supplied to Withdrawal operation
    DuplicateValidatorIndex,
    /// Number of Signatures & Validator Indexes are not same
    InvalidNumberOfSignaturesAndIndexes,
    /// Number of supplied signatures is less than required minimum number of signatures
    NotEnoughSignaturesSupplied,
    /// Validator signature is invalid
    InvalidSignature,
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
        self.validators.push(validator);
        self.version += 1;
    }

    /// Update the state removing an operator for a given token id and address.
    /// Succeeds even if the `operator` is not an operator for this `token_id`
    /// and `address`.
    fn remove_validator(&mut self, validator: &[u8; 33]) {
        for i in 0..self.validators.len() {
            if self.validators[i].eq(validator) {
                self.validators.remove(i);
                break;
            }
        }

        self.version += 1;
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

    ensure!(params.expiration > ctx.metadata().slot_time().timestamp_millis(), ContractError::WithdrawalIsExpired);
    ensure!(params.signatures.len() == params.indexes.len(), ContractError::InvalidNumberOfSignaturesAndIndexes);
    ensure!(params.signatures.len() >= host.state().validators_required.into(), ContractError::NotEnoughSignaturesSupplied);

    ensure!(host.state().is_executed_withdrawal_request(&params.id), ContractError::WithdrawalIsAlreadyExecuted);

    let mut message: Vec<u8> = vec![];

    message.extend(host.state().version.to_le_bytes());
    message.extend(params.id.to_vec());

    match params.to {
        Address::Account(address) => {
            message.extend(address.0);
        },
        Address::Contract(contract) => {
            message.extend(contract.index.to_le_bytes());
            message.extend(contract.subindex.to_le_bytes());
        }
    }

    message.extend(params.amount.to_le_bytes());
    message.extend(params.expiration.to_le_bytes());

    let hash = crypto_primitives.hash_keccak_256(message.as_slice());

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
    ).unwrap_abort();

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
    ).unwrap_abort();

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