// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Nicks Module
//!
//! - [`nicks::Config`](./trait.Config.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! Nicks is an example module for keeping track of account names on-chain. It makes no effort to
//! create a name hierarchy, be a DNS replacement or provide reverse lookups. Furthermore, the
//! weights attached to this module's dispatchable functions are for demonstration purposes only and
//! have not been designed to be economically secure. Do not use this pallet as-is in production.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! * `set_name` - Set the associated name of an account; a small deposit is reserved if not already
//!   taken.
//! * `clear_name` - Remove an account's associated name; the deposit is returned.
//! * `kill_name` - Forcibly remove the associated name; the deposit is lost.
//!
//! [`Call`]: ./enum.Call.html
//! [`Config`]: ./trait.Config.html

#![recursion_limit = "128"]
#![cfg_attr(not(feature = "std"), no_std)]
use codec::{Decode, Encode};
pub use pallet::*;
use sp_runtime::{
	traits::{Dispatchable}
};
use frame_support::{
	ensure,
	traits::{
		schedule::{Named as ScheduleNamed},
		Get},
		weights::Weight,
	
};
use sp_std::prelude::*;
use sp_runtime::{
	DispatchError, RuntimeDebug,
};

// pub use pallet_identity;
pub type PropIndex = u32;

// A value placed in storage that represents the current version of the Democracy storage.
// This value is used by the `on_runtime_upgrade` logic to determine whether we run
// storage migration logic.
#[derive(Encode, Decode, Clone, Copy, PartialEq, Eq, RuntimeDebug)]
enum Releases {
	V1,
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{
		pallet_prelude::*,
		traits::EnsureOrigin,
		Parameter,
		inherent::Vec,
	};
	use frame_system::{ensure_signed, pallet_prelude::*};
	use sp_runtime::DispatchResult;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config + Sized {
		type Proposal: Parameter + Dispatchable<Origin = Self::Origin> + From<Call<Self>>;
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
		
		#[pallet::constant]
		type VotingPeriod: Get<Self::BlockNumber>;
		/// Origin from which proposals may be blacklisted.
		type BlacklistOrigin: EnsureOrigin<Self::Origin>;

		/// Origin from which a proposal may be cancelled and its backers slashed.
		type CancelProposalOrigin: EnsureOrigin<Self::Origin>;
		// type VetoOrigin: EnsureOrigin<Self::Origin, Success = Self::AccountId>;

		/// Period in blocks where an external proposal may not be re-submitted after being vetoed.
		#[pallet::constant]
		type CooloffPeriod: Get<Self::BlockNumber>;
		/// The Scheduler.
		type Scheduler: ScheduleNamed<Self::BlockNumber, Self::Proposal, Self::PalletsOrigin>;

		/// Overarching type of all pallets origins.
		type PalletsOrigin: From<frame_system::RawOrigin<Self::AccountId>>;

		/// The maximum number of votes for an account.
		///
		/// Also used to compute weight, an overly big value can
		/// lead to extrinsic with very big weight: see `delegate` for instance.
		#[pallet::constant]
		type MaxVotes: Get<u32>;

		#[pallet::constant]
		type MaxProposals: Get<u32>;

		
	}


	#[pallet::storage]
	#[pallet::getter(fn public_prop_count)]
	pub type PublicPropCount<T> = StorageValue<_, PropIndex, ValueQuery>;

	/// The public proposals. Unsorted. The second item is the proposal's hash.
	#[pallet::storage]
	#[pallet::getter(fn public_props)]
	pub type PublicProps<T: Config> =
		StorageValue<_, Vec<(PropIndex, Vec<u8>, T::AccountId)>, ValueQuery>;
	//ledger of all votes
	#[pallet::storage]
	#[pallet::getter(fn prop_ledger)]
	pub type PropLedger<T: Config> = 
	 	StorageValue<_, Vec<(PropIndex, bool, T::AccountId, T::BlockNumber)>, ValueQuery>;
	
	
	//TODO investigate: maybe we need this

	 // #[pallet::storage]
	// pub type VotingOf<T: Config> = StorageMap<
	// 	_,
	// 	Twox64Concat,
	// 	T::AccountId,
	// 	Voting<T::AccountId, T::BlockNumber>,
	// 	ValueQuery,
	// >;


	/// A record of who vetoed what. Maps proposal hash to a possible existent block number
	/// (until when it may not be resubmitted) and who vetoed it.
	#[pallet::storage]
	pub type Blacklist<T: Config> =
		StorageMap<_, Identity, Vec<u8>, (T::BlockNumber, Vec<T::AccountId>)>;

	/// Record of all proposals that have been subject to emergency cancellation.
	#[pallet::storage]
	pub type Cancellations<T: Config> = StorageMap<_, Identity, T::Hash, bool, ValueQuery>;

	#[pallet::storage]
	pub(crate) type StorageVersion<T> = StorageValue<_, Releases>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		_phantom: sp_std::marker::PhantomData<T>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			GenesisConfig { _phantom: Default::default() }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			PublicPropCount::<T>::put(0 as PropIndex);
			StorageVersion::<T>::put(Releases::V1);
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
				/// Weight: see `begin_block`
				fn on_initialize(n: T::BlockNumber) -> Weight {
					Self::begin_block(n).unwrap_or_else(|e| {
						sp_runtime::print(e);
						0
					})
				}

	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Introduce an article
		///
		/// The dispatch origin of this call must be _Signed_ and the sender must
		/// have funds to cover the deposit.
		///
		/// - `article_cid`: The CID of file, with article information in json format,
		///  uploaded to IPFS.
		/// 
		///  
		/// Emits `Proposed`.
		///
		/// Weight: `O(p)`
		#[pallet::weight(0)]
		pub fn propose(
			origin: OriginFor<T>,
			article_cid: Vec<u8>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let index = Self::public_prop_count();
			let real_prop_count = PublicProps::<T>::decode_len().unwrap_or(0) as u32;
			let max_proposals = T::MaxProposals::get();
			ensure!(real_prop_count < max_proposals, Error::<T>::TooManyProposals);
			// let Id = <IdentityOf<T>>::get(&who);
			if let Some((until, _)) = <Blacklist<T>>::get(&article_cid) {
				ensure!(
					<frame_system::Pallet<T>>::block_number() >= until,
					Error::<T>::ProposalBlacklisted,
				);
			}
			//TODO make sure user is in good standing by registrar 
			// ensure!(Id.iter().any(|&i| i==Reasonable), Error::<T>::NotIdentified);


			PublicPropCount::<T>::put(index + 1);

			<PublicProps<T>>::append((index, article_cid, who));

			Self::deposit_event(Event::<T>::Proposed(index));
			Ok(())
		}

		// #[pallet::weight(0)]
		// pub fn Vote(origin: OriginFor<T>, ind: PropIndex, vote: bool) -> DispatchResult {
		// 	let who = ensure_signed(origin)?;
		// 		// if let Some((until, _)) = <PropLedger<T>>::get(&who) {
		// 		// 	Ok(())
		// 		// }
		// 	Ok(())
		// }

	}


	



	


	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	#[pallet::metadata(
		T::AccountId = "AccountId",
		Vec<T::AccountId> = "Vec<AccountId>",
		T::BlockNumber = "BlockNumber",
		T::Hash = "Hash",
	)]
	// pub enum Event<T> where AccountId = <T as frame_system::Config>::AccountId, Balance = BalanceOf<T> {
	pub enum Event<T: Config> {
		Proposed(PropIndex),
	}

	/// Error for the nicks module.
	#[pallet::error]
	pub enum Error<T> {
		/// A name is too short.
		TooShort,
		/// A name is too long.
		TooLong,
		/// An account isn't named.
		Unnamed,
		TooManyProposals,
		ProposalBlacklisted,

        AlreadyVote,
        NotIdentified,


	}





	
}

impl<T: Config> Pallet<T> {
	//TODO maybe fix this, temporary fix. Need to investigate making voting free. 
	fn begin_block(_now: T::BlockNumber) -> Result<Weight, DispatchError> {
		let _max_block_weight = T::BlockWeights::get().max_block;
		let weight = 0;


		Ok(weight)
	}
}
#[cfg(test)]
mod tests {
	use super::*;
	use frame_support::traits::GenesisBuild;
	use crate as pallet_nicks;

	use frame_support::{
		assert_ok, assert_noop, impl_outer_origin, parameter_types,
		ord_parameter_types
	};
	use sp_core::H256;
	use frame_system::EnsureSignedBy;
	use sp_runtime::{
		testing::Header, traits::{BlakeTwo256, IdentityLookup, BadOrigin},
	};

	impl_outer_origin! {
		pub enum Origin for Test where system = frame_system {}
	}

	type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<(), (), (), ()>;

	frame_support::impl_outer_event!(
		pub enum Event for Test {
			#[codec(index = "0")] pallet_nicks<T>,
		}
	);

	frame_support::impl_runtime_metadata!(
		for Test with modules where Extrinsic = UncheckedExtrinsic
			pallet_nicks::Module as Nicks { index 0 } with Storage Call Event,
	);

	#[test]
	fn test_metadata() {
		println!("{:#?}", Test::metadata());
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub BlockWeights: frame_system::limits::BlockWeights =
			frame_system::limits::BlockWeights::simple_max(1024);
	}
	impl frame_system::Config for Test {
		type BaseCallFilter = ();
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = ();
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type Version = ();
		type PalletInfo = ();
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
	}
	impl pallet_balances::Config for Test {
		type MaxLocks = ();
		type Balance = u64;
		type Event = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
		type WeightInfo = ();
	}
	parameter_types! {
		pub const ReservationFee: u64 = 2;
		pub const MinLength: u32 = 3;
		pub const MaxLength: u32 = 16;
	}
	ord_parameter_types! {
		pub const One: u64 = 1;
	}
	impl Config for Test {
		type Event = ();
		type Currency = Balances;
		type ReservationFee = ReservationFee;
		type Slashed = ();
		type ForceOrigin = EnsureSignedBy<One, u64>;
		type MinLength = MinLength;
		type MaxLength = MaxLength;
	}
	type System = frame_system::Module<Test>;
	type Balances = pallet_balances::Module<Test>;
	type Nicks = Module<Test>;

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> {
			balances: vec![
				(1, 10),
				(2, 10),
			],
		}.assimilate_storage(&mut t).unwrap();
		pallet_nicks::GenesisConfig::<Test> {
			example_storage: 4u32,
			initial_names: vec![],
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn kill_name_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Nicks::set_name(Origin::signed(2), b"Dave".to_vec()));
			assert_eq!(Balances::total_balance(&2), 10);
			assert_ok!(Nicks::kill_name(Origin::signed(1), 2));
			assert_eq!(Balances::total_balance(&2), 8);
			assert_eq!(<NameOf<Test>>::get(2), None);
		});
	}

	#[test]
	fn force_name_should_work() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				Nicks::set_name(Origin::signed(2), b"Dr. David Brubeck, III".to_vec()),
				Error::<Test>::TooLong,
			);

			assert_ok!(Nicks::set_name(Origin::signed(2), b"Dave".to_vec()));
			assert_eq!(Balances::reserved_balance(2), 2);
			assert_ok!(Nicks::force_name(Origin::signed(1), 2, b"Dr. David Brubeck, III".to_vec()));
			assert_eq!(Balances::reserved_balance(2), 2);
			assert_eq!(<NameOf<Test>>::get(2).unwrap(), (b"Dr. David Brubeck, III".to_vec(), 2));
		});
	}

	#[test]
	fn normal_operation_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Nicks::set_name(Origin::signed(1), b"Gav".to_vec()));
			assert_eq!(Balances::reserved_balance(1), 2);
			assert_eq!(Balances::free_balance(1), 8);
			assert_eq!(<NameOf<Test>>::get(1).unwrap().0, b"Gav".to_vec());

			assert_ok!(Nicks::set_name(Origin::signed(1), b"Gavin".to_vec()));
			assert_eq!(Balances::reserved_balance(1), 2);
			assert_eq!(Balances::free_balance(1), 8);
			assert_eq!(<NameOf<Test>>::get(1).unwrap().0, b"Gavin".to_vec());

			assert_ok!(Nicks::clear_name(Origin::signed(1)));
			assert_eq!(Balances::reserved_balance(1), 0);
			assert_eq!(Balances::free_balance(1), 10);
		});
	}

	#[test]
	fn error_catching_should_work() {
		new_test_ext().execute_with(|| {
			assert_noop!(Nicks::clear_name(Origin::signed(1)), Error::<Test>::Unnamed);

			assert_noop!(
				Nicks::set_name(Origin::signed(3), b"Dave".to_vec()),
				pallet_balances::Error::<Test, _>::InsufficientBalance
			);

			assert_noop!(Nicks::set_name(Origin::signed(1), b"Ga".to_vec()), Error::<Test>::TooShort);
			assert_noop!(
				Nicks::set_name(Origin::signed(1), b"Gavin James Wood, Esquire".to_vec()),
				Error::<Test>::TooLong
			);
			assert_ok!(Nicks::set_name(Origin::signed(1), b"Dave".to_vec()));
			assert_noop!(Nicks::kill_name(Origin::signed(2), 1), BadOrigin);
			assert_noop!(Nicks::force_name(Origin::signed(2), 1, b"Whatever".to_vec()), BadOrigin);
		});
	}
}
