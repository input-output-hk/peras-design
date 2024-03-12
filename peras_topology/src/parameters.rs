use serde::{Deserialize, Serialize};

pub type Currency = u64;

pub type Slot = u64;

#[derive(Debug, Clone, Deserialize, PartialEq, Serialize)]
#[allow(non_snake_case)]
pub struct Parameters {
    pub randomSeed: u64,
    pub endSlot: Slot,
    pub peerCount: usize,
    pub downstreamCount: usize,
    pub totalStake: Option<Currency>,
    pub maximumStake: Currency,
    pub messageDelay: i64,
}

impl Default for Parameters {
    fn default() -> Self {
        Parameters {
            randomSeed: 12345,
            peerCount: 10,
            downstreamCount: 3,
            totalStake: None,
            maximumStake: 1000,
            endSlot: 1000,
            messageDelay: 350000,
        }
    }
}
