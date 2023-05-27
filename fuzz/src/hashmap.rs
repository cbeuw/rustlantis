use std::{collections::HashMap, hash::BuildHasher};

use bimap::BiHashMap;
use rand_seeder::SipHasher;

pub struct StableRandomState;

impl BuildHasher for StableRandomState {
    type Hasher = SipHasher;

    fn build_hasher(&self) -> Self::Hasher {
        SipHasher::new()
    }
}

pub type StableHashMap<K, V> = HashMap<K, V, StableRandomState>;
pub type StableBiHashMap<L, R> = BiHashMap<L, R, StableRandomState, StableRandomState>;