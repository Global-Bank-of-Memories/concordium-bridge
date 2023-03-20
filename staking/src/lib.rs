#![cfg_attr(not(feature = "std"), no_std)]

use std::collections::BTreeMap;
use concordium_cis2::{AdditionalData, CIS0_STANDARD_IDENTIFIER, Receiver, StandardIdentifier, StandardIdentifierOwned, SupportResult, SupportsQueryParams, SupportsQueryResponse, TokenAmountU64, TokenIdUnit, Transfer, TransferParams};
use concordium_std::{*};
use wgbm_shared::{OnReceivingCis2Parameter, TransferParameter};

/// Tag for the NewAdmin event.
pub const NEW_ADMIN_EVENT_TAG: u8 = 0;
pub const STAKED_EVENT_TAG: u8 = 1;
pub const UNSTAKED_EVENT_TAG: u8 = 2;
pub const HARVESTED_REWARDS_EVENT_TAG: u8 = 3;
pub const CREATED_POOL_EVENT_TAG: u8 = 4;

pub const REWARD_MULTIPLIER: u64 = 1000000;
pub const BLOCK_TIMESTAMP_DIVISOR: u64 = 1000;

/// List of supported standards by this contract address.
const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 1] =
    [CIS0_STANDARD_IDENTIFIER];

// Types

/// Contract token ID type.
/// Since this contract will only ever contain this one token type, we use the
/// smallest possible token ID.
type ContractTokenId = TokenIdUnit;

#[derive(Serial, DeserialWithState, Deletable, StateClone)]
#[concordium(state_parameter = "S")]
struct PoolState<S> {
    id: u32,
    reward_tokens_per_block: u64,
    tokens_staked: u64,
    last_rewarded_block: u64,
    accumulated_rewards_per_share: u64,
    stakers: StateSet<Address, S>,
}

#[derive(Serial, Deserial)]
struct PoolStaker {
    amount: u64,
    rewards: u64,
    reward_debt: u64,
}

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
    /// Registered pools
    pools: StateMap<u32, PoolState<S>, S>,
    /// Stakers to pools
    pool_stakers: StateMap<u32, StateMap<Address, PoolStaker, S>, S>,
    /// last id of registered pool
    last_pool_id: u32,
    /// Map with contract addresses providing implementations of additional
    /// standards.
    implementors: StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
}

/// The parameter type for the contract initialization.
#[derive(Serialize, SchemaType)]
struct InitParams {
    token: ContractAddress,
    token_id: ContractTokenId,
}

/// The parameter type for the pool creation.
#[derive(Serialize, SchemaType)]
struct CreatePoolParams {
    reward_tokens_per_block: u64,
}

/// The parameter type for the contract function `unwrap`.
/// Takes an amount of tokens and unwraps the CCD and sends it to a receiver.
#[derive(Serialize, SchemaType)]
struct StakeParams {
    // pool id to unstake
    pool_id: u32,
    // amount of tokens to stake
    amount: u64,
    // entrypoint name in case if sender is contract
    owned_entrypoint_name: String,
}

/// The parameter type for the contract function `unstake`.
/// It includes a receiver for receiving the wrapped CCD tokens.
#[derive(Serialize, SchemaType)]
struct UnstakeParams {
    // pool id to unstake
    pool_id: u32,
    // entrypoint name in case if sender is contract
    owned_entrypoint_name: String,
}

/// The parameter type for the contract function `harvest_rewards`.
/// It includes a receiver for receiving the wrapped CCD tokens.
#[derive(Serialize, SchemaType)]
struct HarvestRewardsParams {
    // pool id to harvest
    pool_id: u32,
    // entrypoint name in case if sender is contract
    owned_entrypoint_name: String,
}

/// The parameter type for the contract function `contract_get_pool_stake`.
/// It includes a receiver for receiving the wrapped CCD tokens.
#[derive(Serialize, SchemaType)]
struct GetPoolStakingParams {
    pool_id: u32,
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
}

/// The return type for the contract function `contract_get_pool_stake`.
#[derive(Serialize, SchemaType)]
struct ReturnPoolStakingDetails {
    staked_amount: u64,
    harvestable_rewards: u64,
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

/// A StakedEvent introduced by this smart contract.
#[derive(Serial, SchemaType, Clone)]
struct StakedEvent {
    // pool_id
    pool_id: u32,
    // sender
    sender: Address,
    // destination: [u8; 256],
    amount: u64,
}

/// A UnstakedEvent introduced by this smart contract.
#[derive(Serial, SchemaType, Clone)]
struct UnstakedEvent {
    pool_id: u32,
    recipient: Address,
    amount: u64,
}

/// A HarvestedRewardsEvent introduced by this smart contract.
#[derive(Serial, SchemaType, Clone)]
struct HarvestedRewardsEvent {
    pool_id: u32,
    recipient: Address,
    amount: u64,
}

/// A PoolCreatedEvent introduced by this smart contract.
#[derive(Serial, SchemaType, Clone)]
struct PoolCreatedEvent {
    pool_id: u32,
}

/// Tagged events to be serialized for the event log.
enum StakingEvent {
    NewAdmin(NewAdminEvent),
    Staked(StakedEvent),
    Unstaked(UnstakedEvent),
    HarvestedRewards(HarvestedRewardsEvent),
    CreatedPool(PoolCreatedEvent),
}

impl Serial for StakingEvent {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        match self {
            StakingEvent::NewAdmin(event) => {
                out.write_u8(NEW_ADMIN_EVENT_TAG)?;
                event.serial(out)
            }
            StakingEvent::Staked(event) => {
                out.write_u8(STAKED_EVENT_TAG)?;
                event.serial(out)
            }
            StakingEvent::Unstaked(event) => {
                out.write_u8(UNSTAKED_EVENT_TAG)?;
                event.serial(out)
            }
            StakingEvent::HarvestedRewards(event) => {
                out.write_u8(HARVESTED_REWARDS_EVENT_TAG)?;
                event.serial(out)
            }
            StakingEvent::CreatedPool(event) => {
                out.write_u8(CREATED_POOL_EVENT_TAG)?;
                event.serial(out)
            }
        }
    }
}

/// Manual implementation of the `StakingEventSchema` which includes both the
/// events specified in this contract and the events specified in the CIS-2
/// library. The events are tagged to distinguish them on-chain.
impl schema::SchemaType for StakingEvent {
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
            STAKED_EVENT_TAG,
            (
                "Staked".to_string(),
                schema::Fields::Named(vec![
                    (String::from("pool_id"), u32::get_type()),
                    (String::from("sender"), Address::get_type()),
                    (String::from("amount"), u64::get_type()),
                ]),
            ),
        );
        event_map.insert(
            UNSTAKED_EVENT_TAG,
            (
                "Unstaked".to_string(),
                schema::Fields::Named(vec![
                    (String::from("pool_id"), u32::get_type()),
                    (String::from("recipient"), Address::get_type()),
                    (String::from("amount"), u64::get_type()),
                ]),
            ),
        );
        event_map.insert(
            HARVESTED_REWARDS_EVENT_TAG,
            (
                "HarvestedRewards".to_string(),
                schema::Fields::Named(vec![
                    (String::from("pool_id"), u32::get_type()),
                    (String::from("recipient"), Address::get_type()),
                    (String::from("amount"), u64::get_type()),
                ]),
            ),
        );
        event_map.insert(
            CREATED_POOL_EVENT_TAG,
            (
                "CreatedPool".to_string(),
                schema::Fields::Named(vec![
                    (String::from("pool_id"), u32::get_type()),
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
    // Unstake amount is zero
    UnstakeAmountIsZero,
    /// Signed Withdrawal operation is expired.
    StakeIsExpired,
    /// Requested stake amount is zero
    StakeAmountIsZero,
    // Referred pool is unknown
    UnknownPool,
    // Referred staker is unknown
    UnknownStaker,
    // Unknown token notified about transfer
    UnknownTokenReceived,
    // Failed to transfer token
    FailedToTransfer
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
    ) -> Self {
        State {
            admin,
            token,
            token_id,
            paused: false,
            pools: state_builder.new_map(),
            pool_stakers: state_builder.new_map(),
            last_pool_id: 0,
            implementors: state_builder.new_map(),
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

    fn create_pool(&mut self, state_builder: &mut StateBuilder<S>, reward_tokens_per_block: u64) -> u32 {
        let pool_id = self.last_pool_id;

        let pool = PoolState {
            id: pool_id,
            reward_tokens_per_block,
            tokens_staked: 0,
            last_rewarded_block: 0,
            accumulated_rewards_per_share: 0,
            stakers: state_builder.new_set()
        };

        self.pools.insert(pool_id, pool);

        self.last_pool_id += 1;

        pool_id
    }

    fn get_pool(&self, pool_id: u32) -> Option<StateRef<PoolState<S>>> {
        self.pools.get(&pool_id)
    }

    fn stake(&mut self, state_builder: &mut StateBuilder<S>, pool_id: u32, user: Address, amount: u64, last_block: u64) -> Result<u64, ContractError> {
        if amount == 0 {
            return Err(ContractError::StakeAmountIsZero);
        }

        if let Some(mut pool) = self.pools.get_mut(&pool_id) {
            let pool: &mut PoolState<S> = &mut pool;

            let pool_stakers = &mut self.pool_stakers.entry(pool_id).or_insert_with(|| state_builder.new_map());

            let pool_staker = &mut pool_stakers.entry(user).or_insert_with(|| {
                pool.stakers.insert(user);

                PoolStaker {
                    amount: 0,
                    rewards: 0,
                    reward_debt: 0,
                }
            });

            let harvested_amount = Self::harvest_rewards_logic(pool, pool_staker, last_block);

            pool_staker.amount += amount;
            pool_staker.reward_debt = pool_staker.amount * pool.accumulated_rewards_per_share / 1;

            pool.tokens_staked += amount;

            return Ok(harvested_amount);
        }

        return Err(ContractError::UnknownPool);
    }

    fn unstake(&mut self, pool_id: u32, user: Address, last_block: u64) -> Result<(u64, u64), ContractError> {
        if let Some(mut pool) = self.pools.get_mut(&pool_id) {
            let pool_stakers = self.pool_stakers.entry(pool_id);

            if let Entry::Occupied(mut pool_stakers) = pool_stakers {
                let pool_staker = pool_stakers.entry(user);

                if let Entry::Occupied(mut pool_staker) = pool_staker {
                    if pool_staker.amount == 0 {
                        return Err(ContractError::UnstakeAmountIsZero);
                    }

                    let harvested_amount = Self::harvest_rewards_logic(&mut pool, &mut pool_staker, last_block);

                    let amount = pool_staker.amount;

                    pool_staker.amount = 0;
                    pool_staker.reward_debt = pool_staker.amount * pool.accumulated_rewards_per_share / REWARD_MULTIPLIER;

                    pool.tokens_staked -= amount;

                    return Ok((amount, harvested_amount));
                } else {
                    return Err(ContractError::UnknownStaker);
                }
            } else {
                return Err(ContractError::UnknownPool);
            }
        }

        return Err(ContractError::UnknownPool);
    }

    fn harvest_rewards(&mut self, pool_id: u32, user: Address, last_block: u64) -> Result<u64, ContractError> {
        if let Some(mut pool) = self.pools.get_mut(&pool_id) {
            let pool_stakers = self.pool_stakers.entry(pool_id);

            if let Entry::Occupied(mut pool_stakers) = pool_stakers {
                let pool_staker = pool_stakers.entry(user);

                if let Entry::Occupied(mut pool_staker) = pool_staker {
                    if pool_staker.amount == 0 {
                        return Ok(0);
                    }

                    let harvested_amount = Self::harvest_rewards_logic(&mut pool, &mut pool_staker, last_block);

                    return Ok(harvested_amount);
                } else {
                    return Err(ContractError::UnknownStaker);
                }
            } else {
                return Err(ContractError::UnknownPool);
            }
        }

        return Err(ContractError::UnknownPool);
    }

    fn calculate_rewards_logic(&self, pool_id: u32, user: Address, last_block: u64) -> Result<u64, ContractError> {
        if let Some(pool) = self.pools.get(&pool_id) {
            let pool_stakers = self.pool_stakers.get(&pool_id);

            if let Some(pool_stakers) = pool_stakers {
                let pool_staker = pool_stakers.get(&user);

                if let Some(pool_staker) = pool_staker {
                    if pool_staker.amount == 0 {
                        return Ok(0);
                    }

                    let blocks_since_last_reward = last_block - pool.last_rewarded_block;

                    let rewards: u64 = blocks_since_last_reward * pool.reward_tokens_per_block;

                    let accumulated_rewards_per_share = pool.accumulated_rewards_per_share + (rewards * REWARD_MULTIPLIER / pool.tokens_staked);

                    let rewards_to_harvest: u64 = (pool_staker.amount * accumulated_rewards_per_share / REWARD_MULTIPLIER) - pool_staker.reward_debt;

                    return Ok(rewards_to_harvest);
                } else {
                    return Err(ContractError::UnknownStaker);
                }
            } else {
                return Err(ContractError::UnknownPool);
            }
        }

        return Err(ContractError::UnknownPool);
    }

    fn harvest_rewards_logic(pool: &mut PoolState<S>, pool_staker: &mut PoolStaker, last_block: u64) -> u64 {
        Self::update_pool_rewards(pool, last_block);

        let rewards_to_harvest: u64 = (pool_staker.amount * pool.accumulated_rewards_per_share / REWARD_MULTIPLIER) - pool_staker.reward_debt;

        if rewards_to_harvest == 0 {
            pool_staker.reward_debt = pool_staker.amount * pool.accumulated_rewards_per_share / REWARD_MULTIPLIER;

            return 0;
        }

        pool_staker.rewards = 0;
        pool_staker.reward_debt = pool_staker.amount * pool.accumulated_rewards_per_share / REWARD_MULTIPLIER;

        return rewards_to_harvest;
    }

    fn update_pool_rewards(pool: &mut PoolState<S>, last_block: u64) {
        if pool.tokens_staked == 0 {
            pool.last_rewarded_block = last_block;

            return;
        }

        let blocks_since_last_reward = last_block - pool.last_rewarded_block;

        let rewards: u64 = blocks_since_last_reward * pool.reward_tokens_per_block;

        pool.accumulated_rewards_per_share = pool.accumulated_rewards_per_share + (rewards * REWARD_MULTIPLIER / pool.tokens_staked);

        pool.last_rewarded_block = last_block;
    }
}

// Contract functions

fn transfer<S: HasStateApi>(host: &mut impl HasHost<State<S>, StateApiType=S>, token: ContractAddress, token_id: ContractTokenId, sender: Address, to: Receiver, amount: u64) -> Result<(), ContractError> {
    let transfer_params: TransferParameter = TransferParams(vec![
        Transfer {
            token_id,
            amount: TokenAmountU64::from(amount),
            /// The address owning the tokens being transferred.
            from: sender,
            /// The address receiving the tokens being transferred.
            to,
            /// Additional data to include in the transfer.
            /// Can be used for additional arguments.
            data: AdditionalData::empty(),
        }
    ]);

    host.invoke_contract(
        &token,
        &transfer_params,
        EntrypointName::new_unchecked("transfer"),
        Amount::zero(),
    ).map_err(|_error| ContractError::FailedToTransfer)?;

    Ok(())
}

/// Initialize contract instance with no initial tokens.
/// Logs a `Mint` event for the single token id with no amounts.
/// Logs a `TokenMetadata` event with the metadata url and hash.
/// Logs a `NewAdmin` event with the invoker as admin.
#[init(
contract = "gbm_Staking",
enable_logger,
parameter = "InitParams",
event = "StakingEvent"
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

    // Construct the initial contract state.
    let state = State::new(state_builder, invoker, token_address, token_id);

    // Log event for the new admin.
    logger.log(&StakingEvent::NewAdmin(NewAdminEvent {
        new_admin: invoker,
    }))?;

    Ok(state)
}

/// Create new pool
#[receive(
contract = "gbm_Staking",
name = "createPool",
parameter = "CreatePoolParams",
error = "ContractError",
mutable,
enable_logger,
)]
fn contract_create_pool<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType=S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    let (state, builder) = host.state_and_builder();

    // Check that contract is not paused.
    ensure!(!state.paused, ContractError::ContractPaused);

    // Check that only the current admin is authorized to update the admin address.
    ensure_eq!(ctx.sender(), state.admin, ContractError::Unauthorized);

    // Parse the parameter.
    let params: CreatePoolParams = ctx.parameter_cursor().get()?;

    let pool_id = state.create_pool(builder, params.reward_tokens_per_block);

    // Log withdrawal.
    logger.log(&StakingEvent::CreatedPool(PoolCreatedEvent {
        pool_id,
    }))?;

    Ok(())
}

/// Unwrap an amount of wGBM tokens into CCD
#[receive(
contract = "gbm_Staking",
name = "transfer_notification",
parameter = "OnReceivingCis2Parameter",
error = "ContractError",
)]
fn contract_transfer_notification<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType=S>
) -> ContractResult<()>
{
    let state = host.state();

    // Check that contract is not paused.
    ensure!(!state.paused, ContractError::ContractPaused);

    let params: OnReceivingCis2Parameter = ctx.parameter_cursor().get()?;

    ensure!(state.token_id == params.token_id, ContractError::UnknownTokenReceived);

    Ok(())
}

/// Unwrap an amount of wGBM tokens into CCD
#[receive(
contract = "gbm_Staking",
name = "stake",
parameter = "StakeParams",
error = "ContractError",
enable_logger,
mutable,

)]
fn contract_stake<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType=S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()>
{
    // Check that contract is not paused.
    ensure!(!host.state().paused, ContractError::ContractPaused);

    // Parse the parameter.
    let params: StakeParams = ctx.parameter_cursor().get()?;

    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    transfer(
        host,
        host.state().token,
        host.state().token_id,
        sender,
        Receiver::Contract(
            ctx.self_address(),
            OwnedEntrypointName::new_unchecked("transfer_notification".to_string())
        ),
        params.amount,
    )?;

    let last_block = ctx.metadata().slot_time().timestamp_millis() / BLOCK_TIMESTAMP_DIVISOR;

    let (state, builder) = host.state_and_builder();

    let result = state.stake(
        builder,
        params.pool_id,
        sender.clone(),
        params.amount,
        last_block
    )?;

    transfer(
        host,
        host.state().token,
        host.state().token_id,
        Address::Contract(ctx.self_address()),
        match sender {
            Address::Account(account) => Receiver::Account(account),
            Address::Contract(contract) => Receiver::Contract(contract, OwnedEntrypointName::new_unchecked(params.owned_entrypoint_name)),
        },
        result,
    )?;

    // Log the deposit of tokens.
    logger.log(&StakingEvent::Staked(StakedEvent {
        pool_id: params.pool_id,
        sender,
        amount: params.amount,
    }))?;

    Ok(())
}

/// Wrap an amount of CCD into wGBM tokens and transfer the tokens if the sender
/// is not the receiver.
#[receive(
contract = "gbm_Staking",
name = "unstake",
parameter = "UnstakeParams",
error = "ContractError",
mutable,
enable_logger,
)]
fn contract_unstake<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType=S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()>
{
    // Check that contract is not paused.
    ensure!(!host.state().paused, ContractError::ContractPaused);

    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    // Parse the parameter.
    let params: UnstakeParams = ctx.parameter_cursor().get()?;

    let last_block = ctx.metadata().slot_time().timestamp_millis() / BLOCK_TIMESTAMP_DIVISOR;
    let result = host.state_mut().unstake(params.pool_id, sender, last_block)?;

    transfer(
        host,
        host.state().token,
        host.state().token_id,
        Address::Contract(ctx.self_address()),
        match sender {
            Address::Account(account) => Receiver::Account(account),
            Address::Contract(contract) => Receiver::Contract(contract, OwnedEntrypointName::new_unchecked(params.owned_entrypoint_name)),
        },
        result.0 + result.1,
    )?;

    // Log withdrawal.
    logger.log(&StakingEvent::Unstaked(UnstakedEvent {
        pool_id: params.pool_id,
        recipient: sender,
        amount: result.0,
    }))?;

    // Log the deposit of tokens.
    logger.log(&StakingEvent::HarvestedRewards(HarvestedRewardsEvent {
        pool_id: params.pool_id,
        recipient: sender,
        amount: result.1,
    }))?;

    Ok(())
}

/// Harvest an amount of wGBM tokens into CCD
#[receive(
contract = "gbm_Staking",
name = "harvestRewards",
parameter = "HarvestRewardsParams",
error = "ContractError",
enable_logger,
mutable
)]
fn contract_harvest_rewards<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType=S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()>
{
    // Check that contract is not paused.
    ensure!(!host.state().paused, ContractError::ContractPaused);

    // Parse the parameter.
    let params: HarvestRewardsParams = ctx.parameter_cursor().get()?;

    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    let last_block = ctx.metadata().slot_time().timestamp_millis() / BLOCK_TIMESTAMP_DIVISOR;

    let result = host.state_mut().harvest_rewards(params.pool_id, sender, last_block)?;

    transfer(
        host,
        host.state().token,
        host.state().token_id,
        Address::Contract(ctx.self_address()),
        match sender {
            Address::Account(account) => Receiver::Account(account),
            Address::Contract(contract) => Receiver::Contract(contract, OwnedEntrypointName::new_unchecked(params.owned_entrypoint_name)),
        },
        result,
    )?;

    // Log the deposit of tokens.
    logger.log(&StakingEvent::HarvestedRewards(HarvestedRewardsEvent {
        pool_id: params.pool_id,
        recipient: sender,
        amount: result,
    }))?;

    Ok(())
}

/// Harvest an amount of wGBM tokens into CCD
#[receive(
contract = "gbm_Staking",
name = "getPoolStaking",
parameter = "GetPoolStakingParams",
return_value = "ReturnPoolStakingDetails",
error = "ContractError",
)]
fn contract_get_pool_staking<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType=S>,
) -> ContractResult<ReturnPoolStakingDetails>
{
    let state = host.state();

    // Check that contract is not paused.
    ensure!(!state.paused, ContractError::ContractPaused);

    // Parse the parameter.
    let params: GetPoolStakingParams = ctx.parameter_cursor().get()?;

    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    let last_block = ctx.metadata().slot_time().timestamp_millis() / BLOCK_TIMESTAMP_DIVISOR;

    let harvestable_rewards = state.calculate_rewards_logic(
        params.pool_id,
        sender,
        last_block
    )?;

    let pool = state.get_pool(params.pool_id).unwrap();

    Ok(ReturnPoolStakingDetails {
        staked_amount: pool.tokens_staked,
        harvestable_rewards,
    })
}

/// Transfer the admin address to a new admin address.
///
/// It rejects if:
/// - Sender is not the current admin of the contract instance.
/// - It fails to parse the parameter.
#[receive(
contract = "gbm_Staking",
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
    logger.log(&StakingEvent::NewAdmin(NewAdminEvent {
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
contract = "gbm_Staking",
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
contract = "gbm_Staking",
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
        }
    )
}

/// Get the supported standards or addresses for a implementation given list of
/// standard identifiers.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
contract = "gbm_Staking",
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
contract = "gbm_Staking",
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
contract = "gbm_Staking",
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

    /// Test helper function which creates a contract state where ADDRESS_0 owns
    /// 400 tokens.
    fn initial_state<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> State<S> {
        let mut state = State::new(
            state_builder,
            ADMIN_ADDRESS,
            ContractAddress::new(100, 100),
            TOKEN_ID,
        );

        state.create_pool(state_builder, 1);

        state
    }

    /// Test stake & unstake function.
    #[concordium_test]
    fn test_stake() {
        // Set up the context.
        let mut ctx = TestReceiveContext::empty();

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        ctx.set_sender(ADDRESS_1);
        // We are simulating reentrancy with this mock because we mutate the state.
        host.setup_mock_entrypoint(
            host.state().token.clone(),
            EntrypointName::new_unchecked("transfer").into(),
            MockFn::new_v1(|parameter, _amount, _balance, _state: &mut State<TestStateApi>| {
                let params: TransferParameter = match from_bytes(parameter.0) {
                    Ok(params) => params,
                    Err(_) => return Err(CallContractError::Trap),
                };

                if params.0[0].from == ADDRESS_1 {
                    return Err(CallContractError::Trap);
                } else if params.0[0].from == ADDRESS_0 {
                    return Ok((true, ()));
                }

                Ok((true, ()))
            }),
        );

        // Set up the parameter.
        let stake_params = StakeParams {
            pool_id: 0,
            amount: 10000u64,
            owned_entrypoint_name: "".to_string(),
        };

        let parameter_bytes = to_bytes(&stake_params);
        ctx.set_parameter(&parameter_bytes);
        ctx.set_self_address(ContractAddress::new(0, 0));
        ctx.set_metadata_slot_time(SlotTime::from_timestamp_millis(TIME_NOW * 1000));

        let result: ContractResult<()> = contract_stake(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_err(), "Results in success");

        ctx.set_sender(ADDRESS_0);

        let result: ContractResult<()> =
            contract_stake(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&StakingEvent::Staked(StakedEvent {
                pool_id: 0,
                sender: ADDRESS_0,
                amount: stake_params.amount,
            })),
            "Incorrect event emitted"
        );

        // Set up the parameter.
        let unstake_params = UnstakeParams {
            pool_id: 0,
            owned_entrypoint_name: "".to_string(),
        };

        let unstake_parameter_bytes = to_bytes(&unstake_params);
        ctx.set_parameter(&unstake_parameter_bytes);
        ctx.set_metadata_slot_time(SlotTime::from_timestamp_millis((TIME_NOW + 86400 * 10) * 1000));

        let result: ContractResult<()> = contract_unstake(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the logs.
        claim_eq!(logger.logs.len(), 3, "Only one event should be logged");

        claim_eq!(
            logger.logs[1],
            to_bytes(&StakingEvent::Unstaked(UnstakedEvent {
                pool_id: 0,
                recipient: ADDRESS_0,
                amount: stake_params.amount,
            })),
            "Incorrect event emitted"
        );

        claim_eq!(
            logger.logs[2],
            to_bytes(&StakingEvent::HarvestedRewards(HarvestedRewardsEvent {
                pool_id: 0,
                recipient: ADDRESS_0,
                amount: 864000,
            })),
            "Incorrect event emitted"
        );
    }

    /// Test harvest_rewards function.
    #[concordium_test]
    fn test_harvest_rewards() {
        // Set up the context.
        let mut ctx = TestReceiveContext::empty();

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        ctx.set_sender(ADDRESS_1);
        // We are simulating reentrancy with this mock because we mutate the state.
        host.setup_mock_entrypoint(
            host.state().token.clone(),
            EntrypointName::new_unchecked("transfer").into(),
            MockFn::new_v1(|parameter, _amount, _balance, _state: &mut State<TestStateApi>| {
                let _params: TransferParameter = match from_bytes(parameter.0) {
                    Ok(params) => params,
                    Err(_) => return Err(CallContractError::Trap),
                };

                Ok((true, ()))
            }),
        );

        // Set up the parameter.
        let stake_params = StakeParams {
            pool_id: 0,
            amount: 10000u64,
            owned_entrypoint_name: "".to_string(),
        };

        let parameter_bytes = to_bytes(&stake_params);
        ctx.set_parameter(&parameter_bytes);
        ctx.set_self_address(ContractAddress::new(0, 0));
        ctx.set_metadata_slot_time(SlotTime::from_timestamp_millis(TIME_NOW * 1000));

        ctx.set_sender(ADDRESS_0);

        let result: ContractResult<()> = contract_stake(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&StakingEvent::Staked(StakedEvent {
                pool_id: 0,
                sender: ADDRESS_0,
                amount: stake_params.amount,
            })),
            "Incorrect event emitted"
        );

        // Set up the parameter.
        let harvest_rewards_params = HarvestRewardsParams {
            pool_id: 0,
            owned_entrypoint_name: "".to_string(),
        };

        let harvest_rewards_parameter_bytes = to_bytes(&harvest_rewards_params);
        ctx.set_parameter(&harvest_rewards_parameter_bytes);
        ctx.set_metadata_slot_time(SlotTime::from_timestamp_millis((TIME_NOW + 86400 * 10) * 1000));

        let result: ContractResult<()> = contract_harvest_rewards(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the logs.
        claim_eq!(logger.logs.len(), 2, "Only one event should be logged");

        claim_eq!(
            logger.logs[1],
            to_bytes(&StakingEvent::HarvestedRewards(HarvestedRewardsEvent {
                pool_id: 0,
                recipient: ADDRESS_0,
                amount: 864000,
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
            logger.logs.contains(&to_bytes(&StakingEvent::NewAdmin(NewAdminEvent {
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