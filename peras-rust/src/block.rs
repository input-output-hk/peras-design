use crate::crypto::{Hash, LeadershipProof, Signature};
use serde::{Deserialize, Serialize};

pub type Slot = u64;

pub type PartyId = u64;

#[derive(Eq, Clone, PartialEq, Debug, Deserialize, Serialize, Hash)]
#[serde(tag = "tag", rename_all = "camelCase")]
pub struct Party {
    pub id: PartyId,
    #[serde(with = "hex::serde")]
    pub vkey: [u8; 8],
}

#[derive(Eq, Clone, PartialEq, Debug, Deserialize, Serialize, Hash)]
#[serde(tag = "tag", rename_all = "camelCase")]
pub struct Tx {}

#[derive(Eq, Clone, PartialEq, Debug, Deserialize, Serialize, Hash)]
#[serde(tag = "tag", rename_all = "camelCase")]
pub struct Block {
    pub slot_number: Slot,
    pub creator_id: PartyId,
    pub parent_block: Hash,
    pub included_votes: Vec<Hash>,
    pub leadership_proof: LeadershipProof,
    pub signature: Signature,
    pub body_hash: Hash,
}

#[derive(Eq, Clone, PartialEq, Debug, Deserialize, Serialize, Hash)]
#[serde(tag = "tag", rename_all = "camelCase")]
pub struct BlockBody {
    pub block_hash: Hash,
    pub payload: Vec<Tx>,
}
