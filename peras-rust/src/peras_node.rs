use std::{
    sync::mpsc::{self, Receiver, Sender},
    thread::{self, JoinHandle},
};

use crate::{
    block::Block,
    chain::{empty_chain, Chain},
    crypto,
    message::{Message, NodeId, OutMessage},
};
use chrono::{DateTime, Utc};
use rand::{rngs::StdRng, Rng, RngCore, SeedableRng};
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "tag", rename_all_fields = "camelCase")]
pub enum InEnvelope {
    /// Kill the receiver
    Stop,

    /// Send a message from some other node
    #[serde(rename = "InEnvelope")]
    SendMessage {
        origin: Option<NodeId>,
        in_message: Message,
    },
}

#[derive(Debug, Deserialize, Serialize)]
pub struct NodeState {}

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "tag", rename_all_fields = "camelCase")]
pub enum OutEnvelope {
    Idle {
        timestamp: DateTime<Utc>,
        source: String,
        best_chain: Chain,
    },
    #[serde(rename = "OutEnvelope")]
    SendMessage {
        timestamp: DateTime<Utc>,
        source: String,
        destination: String,
        out_message: OutMessage,
        bytes: u32,
    },
}

pub struct NodeParameters {
    pub node_stake: u64,
    pub total_stake: u64,
    pub active_coefficient: f64,
}

impl Default for NodeParameters {
    fn default() -> Self {
        NodeParameters {
            node_stake: 10,
            total_stake: 100,
            active_coefficient: 0.05,
        }
    }
}

pub struct Node {
    node_id: NodeId,
    parameters: NodeParameters,
    seed: StdRng,
    best_chain: Chain,
}

pub struct NodeHandle {
    sender: Sender<InEnvelope>,
    receiver: Receiver<OutEnvelope>,
    thread: Option<JoinHandle<()>>,
}

impl Node {
    pub fn new(node_id: NodeId, parameters: NodeParameters) -> Self {
        Node {
            node_id,
            parameters,
            seed: StdRng::seed_from_u64(12),
            best_chain: empty_chain(),
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

    // FIXME: why is the slot number not involved in the leadership selection?
    fn is_slot_leader(&mut self, _slot: u64) -> bool {
        let stake_ratio =
            (self.parameters.node_stake as f64) / (self.parameters.total_stake as f64);
        let prob = 1.0 - (1.0 - self.parameters.active_coefficient).powf(stake_ratio);
        self.seed.gen_bool(prob)
    }
}

fn work(mut node: Node, rx_in: Receiver<InEnvelope>, tx_out: Sender<OutEnvelope>) {
    loop {
        let recv = rx_in.recv();
        match recv {
            Ok(InEnvelope::Stop) => return,
            Ok(InEnvelope::SendMessage {
                origin: _,
                in_message: Message::NextSlot(slot),
            }) => match handle_slot(slot, &mut node) {
                Some(out) => tx_out.send(out).expect("Failed to send message"),
                None => (),
            },
            Ok(_) => (),
            Err(err) => panic!("Error while receiving message {err}"),
        }

        tx_out
            .send(OutEnvelope::Idle {
                timestamp: Utc::now(),
                source: node.node_id.clone(),
                best_chain: node.best_chain.clone(),
            })
            .expect("Failed to send Idle message")
    }
}

fn handle_slot(slot: u64, node: &mut Node) -> Option<OutEnvelope> {
    if node.is_slot_leader(slot) {
        let mut signature = [0u8; 8];
        node.seed.fill_bytes(&mut signature);
        let mut leadership_proof = [0u8; 8];
        node.seed.fill_bytes(&mut leadership_proof);
        let new_block = Block {
            slot_number: slot,
            creator_id: 1,
            parent_block: crypto::Hash {
                hash: [0, 0, 0, 0, 0, 0, 0, 0],
            },
            included_votes: vec![],
            leadership_proof: crypto::LeadershipProof {
                proof: leadership_proof,
            },
            payload: vec![],
            signature: crypto::Signature { signature },
        };
        node.best_chain.blocks.insert(0, new_block);
        Some(OutEnvelope::SendMessage {
            timestamp: Utc::now(),
            source: node.node_id.clone(),
            destination: node.node_id.clone(), // FIXME this does not make sense
            out_message: OutMessage::SendMessage(Message::NewChain(node.best_chain.clone())),
            bytes: 0,
        })
    } else {
        None
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
    use super::*;
    use std::{fs::File, io::BufReader, path::Path};

    #[derive(Debug, Deserialize, Serialize)]
    struct Golden<T> {
        samples: Vec<T>,
    }

    #[test]
    fn can_deserialize_chain_from_json() {
        let curfile = file!();
        // FIXME: having hardcoded relative path is not great for maintainability
        // and portability
        let golden_path = Path::new(curfile)
            .parent()
            .unwrap()
            .join("../../peras-hs/golden/Chain.json");
        let golden_file = File::open(golden_path).expect("Unable to open file");
        let reader = BufReader::new(golden_file);
        let result: Result<Golden<Chain>, _> = serde_json::from_reader(reader);

        if let Err(err) = result {
            println!("{}", err);
            assert!(false);
        }
    }

    /// FIXME: InEnvelope is incomplete, deserialisation from golden file will fail
    fn can_deserialize_messages_from_json() {
        let curfile = file!();
        // FIXME: having hardcoded relative path is not great for maintainability
        // and portability
        let golden_path = Path::new(curfile)
            .parent()
            .unwrap()
            .join("../../peras-iosim/golden/InEnvelope.json");
        let golden_file = File::open(golden_path).expect("Unable to open file");
        let reader = BufReader::new(golden_file);
        let result: Result<Golden<InEnvelope>, _> = serde_json::from_reader(reader);

        if let Err(err) = result {
            println!("{}", err);
            assert!(false);
        }
    }

    #[test]
    fn returns_idle_after_processing_tick() {
        let node = Node::new("N1".into(), Default::default());
        let mut handle = node.start();

        handle.send(InEnvelope::SendMessage {
            origin: None,
            in_message: Message::NextSlot(1),
        });

        let received = handle.receive();

        handle.stop(); // should be in some teardown method

        match received {
            OutEnvelope::Idle {
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
        let params = NodeParameters {
            node_stake: 100,
            total_stake: 100,
            active_coefficient: 1.0,
        };
        let mut node = Node::new("N1".into(), params);

        assert!(node.is_slot_leader(slot))
    }

    #[test]
    fn node_is_slot_leader_every_other_slot_given_coefficient_is_0_5_and_node_has_all_stake() {
        let params = NodeParameters {
            node_stake: 100,
            total_stake: 100,
            active_coefficient: 0.5,
        };
        let mut node = Node::new("N1".into(), params);
        let schedule = (0..10000)
            .map(|n| node.is_slot_leader(n))
            .filter(|b| *b)
            .count();

        assert_eq!(schedule.div_ceil(100), 51);
    }

    #[test]
    fn node_is_slot_leader_every_slot_given_coefficient_is_1_and_node_has_half_the_stake() {
        let params = NodeParameters {
            node_stake: 50,
            total_stake: 100,
            active_coefficient: 1.0,
        };
        let mut node = Node::new("N1".into(), params);

        let schedule = (0..100)
            .map(|n| node.is_slot_leader(n))
            .filter(|b| *b)
            .count();

        // NOTE: this is counterintuitive but a consequence of the slot leader election formula
        assert_eq!(schedule, 100);
    }

    #[test]
    fn node_is_slot_leader_every_3_slots_given_coefficient_is_0_5_and_node_has_half_the_stake() {
        let params = NodeParameters {
            node_stake: 50,
            total_stake: 100,
            active_coefficient: 0.5,
        };
        let mut node = Node::new("N1".into(), params);

        let schedule = (0..10000)
            .map(|n| node.is_slot_leader(n))
            .filter(|b| *b)
            .count();

        assert_eq!(schedule.div_ceil(100), 30);
    }

    #[test]
    fn produce_a_block_when_node_is_leader() {
        let params = NodeParameters {
            node_stake: 50,
            total_stake: 100,
            active_coefficient: 1.0,
        };
        let node = Node::new("N1".into(), params);
        let mut handle = node.start();

        for i in 1..5 {
            handle.send(InEnvelope::SendMessage {
                origin: None,
                in_message: Message::NextSlot(i),
            })
        }

        let received = handle.receive();

        handle.stop(); // should be in some teardown method

        match received {
            OutEnvelope::SendMessage {
                timestamp: _,
                source: _,
                destination: _,
                out_message: OutMessage::SendMessage(Message::NewChain(chain)),
                bytes: _,
            } => {
                println!("got chain {:?}", serde_json::to_string(&chain));
                assert_ne!(chain, empty_chain());
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn grow_best_chain_from_the_head() {
        let params = NodeParameters {
            node_stake: 100,
            total_stake: 100,
            active_coefficient: 1.0,
        };
        let node = Node::new("N1".into(), params);
        let mut handle = node.start();

        for i in 1..5 {
            handle.send(InEnvelope::SendMessage {
                origin: None,
                in_message: Message::NextSlot(i),
            })
        }

        // we expect some Idle + NewChain messages
        for i in 1..8 {
            let _ = handle.receive();
        }

        let received = handle.receive();

        handle.stop(); // should be in some teardown method

        match received {
            OutEnvelope::Idle {
                timestamp: _,
                source: _,
                best_chain: Chain { blocks, votes },
            } => {
                let slots: Vec<u64> = blocks.iter().map(|b| b.slot_number).collect();
                assert!(slots.windows(2).all(|w| w[0] > w[1]));
            }
            _ => assert!(false),
        }
    }
}
