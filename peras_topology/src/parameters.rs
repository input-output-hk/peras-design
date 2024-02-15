use serde::{Deserialize, Serialize};

pub type Currency = u64;

pub type Slot = u64;

pub type Seed = u64;

#[derive(Debug, Clone, Deserialize, PartialEq, Serialize)]
#[allow(non_snake_case)]
pub struct Parameters {
    pub randomSeed: Seed,
    pub endSlot: Slot,
    pub peerCount: usize,
    pub downstreamCount: usize,
    pub totalStake: Option<Currency>,
    pub maximumStake: Currency,
    pub messageDelay: f64,
}
