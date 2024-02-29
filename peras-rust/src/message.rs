use serde::{Deserialize, Serialize};

use crate::block::{Block, Slot};
use crate::chain::Chain;

pub type NodeId = String;

#[derive(Debug, Deserialize, Serialize)]
pub enum Message {
    NextSlot(Slot),
    SomeBlock(Block),
    NewChain(Chain),
}
