use std::{
    sync::mpsc::{self, Receiver, Sender},
    thread::{self, JoinHandle},
};

use crate::{chain::Chain, message::NodeId};
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize)]
pub enum InEnvelope {
    /// Kill the receiver
    PoisonPill,
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
}

pub struct NodeHandle {
    sender: Sender<InEnvelope>,
    receiver: Receiver<OutEnvelope>,
    thread: Option<JoinHandle<()>>,
}

impl Node {
    pub fn new(node_id: NodeId, node_stake: u64) -> Self {
        Node {
            node_id,
            node_stake,
        }
    }

    pub fn start(&self) -> NodeHandle {
        let (tx_in, rx_in) = mpsc::channel::<InEnvelope>();
        let (tx_out, rx_out) = mpsc::channel::<OutEnvelope>();

        let thread = thread::spawn(move || work(rx_in, tx_out));

        println!("starting node");

        NodeHandle {
            sender: tx_in,
            receiver: rx_out,
            thread: Some(thread),
        }
    }
}

fn work(rx_in: Receiver<InEnvelope>, tx_out: Sender<OutEnvelope>) {
    todo!()
}

impl NodeHandle {
    pub fn stop(&mut self) {
        if self.thread.as_ref().map_or(false, |t| t.is_finished()) {
            return;
        }
        self.sender
            .send(InEnvelope::PoisonPill)
            .expect("sending poison pill failed");
        self.thread.take().unwrap().join().expect("node stopped");
    }

    pub fn send(&mut self, msg: InEnvelope) {
        self.sender.send(msg).expect("sending failed");
    }

    pub fn receive(&mut self) -> Option<OutEnvelope> {
        self.receiver.try_recv().ok()
    }
}

#[cfg(test)]
mod tests {
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
}
