use std::{
    sync::mpsc::{self, Receiver, Sender},
    thread::{self, JoinHandle},
};

use crate::{
    chain::{empty_chain, Chain},
    message::{Message, NodeId},
};
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize)]
pub enum InEnvelope {
    /// Kill the receiver
    Stop,

    /// Send a message from some other node
    SendMessage {
        origin: Option<NodeId>,
        message: Message,
    },
}

#[derive(Debug, Deserialize, Serialize)]
pub struct NodeState {}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all_fields = "camelCase")]
pub enum OutEnvelope {
    Idle {
        timestamp: DateTime<Utc>,
        source: String,
        best_chain: Chain,
    },
}

pub struct Node {
    node_id: NodeId,
    node_stake: u64,
    total_stake: u64,
}

pub struct NodeHandle {
    sender: Sender<InEnvelope>,
    receiver: Receiver<OutEnvelope>,
    thread: Option<JoinHandle<()>>,
}

impl Node {
    pub fn new(node_id: NodeId, node_stake: u64, total_stake: u64) -> Self {
        Node {
            node_id,
            node_stake,
            total_stake,
        }
    }

    pub fn start(self) -> NodeHandle {
        let (tx_in, rx_in) = mpsc::channel::<InEnvelope>();
        let (tx_out, rx_out) = mpsc::channel::<OutEnvelope>();

        let thread = thread::spawn(move || work(self, rx_in, tx_out));

        NodeHandle {
            sender: tx_in,
            receiver: rx_out,
            thread: Some(thread),
        }
    }

    pub fn is_slot_leader(&self, slot: u64) -> bool {
        true
    }
}

fn work(node: Node, rx_in: Receiver<InEnvelope>, tx_out: Sender<OutEnvelope>) {
    println!("starting node");
    loop {
        let recv = rx_in.recv();
        match recv {
            Ok(InEnvelope::Stop) => return,
            Ok(InEnvelope::SendMessage {
                origin: _,
                message: Message::NextSlot(slot),
            }) => tx_out
                .send(OutEnvelope::Idle {
                    timestamp: Utc::now(),
                    source: node.node_id.clone(),
                    best_chain: empty_chain(),
                })
                .expect("Failed to send message"),
            Ok(_) => (),
            Err(err) => panic!("Error while receiving message {err}"),
        }
    }
}

impl NodeHandle {
    pub fn stop(&mut self) {
        if self.thread.as_ref().map_or(false, |t| t.is_finished()) {
            return;
        }
        self.sender
            .send(InEnvelope::Stop)
            .expect("sending poison pill failed");
        self.thread.take().unwrap().join().expect("node stopped");
    }

    pub fn send(&mut self, msg: InEnvelope) {
        self.sender.send(msg).expect("sending failed");
    }

    /// Non blocking receiving of a message from the node
    pub fn try_receive(&mut self) -> Option<OutEnvelope> {
        self.receiver.try_recv().ok()
    }

    /// Blocking receiving of a message from anode
    pub fn receive(&mut self) -> OutEnvelope {
        self.receiver.recv().expect("failed to receive message")
    }
}

#[cfg(test)]
mod tests {
    use crate::chain::empty_chain;
    extern crate quickcheck;

    use super::InEnvelope::*;
    use super::OutEnvelope::*;
    use std::{fs::File, io::BufReader, path::Path};

    use super::*;

    #[derive(Debug, Deserialize, Serialize)]
    struct Golden<T> {
        samples: Vec<T>,
    }

    #[test]
    fn can_deserialize_chain_from_json() {
        let curfile = file!();
        // FIXME: having hardcoded relative path is not greatt for maintainability
        // and portability
        let golden_path = Path::new(curfile)
            .parent()
            .unwrap()
            .join("../../peras-hs/golden/Chain.json");
        println!("file: {:?}", golden_path);
        let golden_file = File::open(golden_path).expect("Unable to open file");
        let reader = BufReader::new(golden_file);
        let result: Result<Golden<Chain>, _> = serde_json::from_reader(reader);

        if let Err(err) = result {
            println!("{}", err);
            assert!(false);
        }
    }

    #[test]
    fn returns_idle_after_processing_tick() {
        let node = Node::new("N1".into(), 42, 100);
        let mut handle = node.start();

        handle.send(SendMessage {
            origin: None,
            message: Message::NextSlot(1),
        });

        let received = handle.receive();

        handle.stop(); // should be in some teardown method

        match received {
            Idle {
                timestamp: _,
                source: _,
                best_chain,
            } => {
                assert_eq!(best_chain, empty_chain());
            }
            _ => assert!(false),
        }
    }

    #[quickcheck_macros::quickcheck]
    fn node_is_slot_leader_every_slot_given_coefficient_is_1_and_node_has_all_stake(slot: u64) {
        let node = Node::new("N1".into(), 100, 100);
        assert!(node.is_slot_leader(slot))
    }

}
