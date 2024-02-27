use crate::{
    block::{Block, PartyId},
    crypto::{Hash, MembershipProof, Signature},
};
use serde::{Deserialize, Serialize};

pub type RoundNumber = u64;

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Vote {
    pub voting_round: RoundNumber,
    pub creator_id: PartyId,
    pub committee_membership_proof: MembershipProof,
    pub block_hash: Hash,
    pub signature: Signature,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct Chain {
    pub blocks: Vec<Block>,
    pub votes: Vec<Vote>,
}
