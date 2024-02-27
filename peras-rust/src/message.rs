use crate::block::{Block, Slot};
use crate::chain::Chain;

pub type NodeId = String;

pub enum Message {
    NextSlot(Slot),
    SomeBlock(Block),
    NewChain(Chain),
}
