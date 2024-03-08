use serde::{Deserialize, Serialize};

use crate::block::{Block, BlockBody, Slot};
use crate::chain::{Chain,Vote};
use crate::crypto::Hash;

pub type NodeId = String;

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "tag", content = "contents")]
pub enum Message {
    NextSlot(Slot),
    NewChain(Chain),
    SomeVote(Vote),
    FetchVotes(Vec<Hash>),
    FollowChain(Hash),
    RollForward(Block),
    RollBack(Block),
    FetchBlocks(Vec<Hash>),
    SomeBlock(BlockBody),
}
