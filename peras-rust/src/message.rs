use serde::{Deserialize, Serialize};

use crate::block::{Block, Slot};
use crate::chain::Chain;

pub type NodeId = String;

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "tag", content = "contents")]
pub enum Message {
    NextSlot(Slot),
    SomeBlock(Block),
    NewChain(Chain),
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "tag", content = "contents")]
pub enum OutMessage {
    FetchBlock(Block),
    SendMessage(Message),
}
