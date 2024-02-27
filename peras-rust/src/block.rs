use crate::crypto::{Hash, LeadershipProof, Signature};
use serde::{Deserialize, Serialize};

pub type Slot = u64;

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "tag", rename_all = "camelCase")]
pub struct PartyId {
    pub id: u64,
    pub vkey: [u8; 8],
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "tag", rename_all = "camelCase")]
pub struct Tx {}

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "tag", rename_all = "camelCase")]
pub struct Block {
    pub slot_number: Slot,
    pub creator_id: PartyId,
    pub parent_block: Hash,
    pub included_votes: Vec<Hash>,
    pub leadership_proof: LeadershipProof,
    pub payload: Vec<Tx>,
    pub signature: Signature,
}
