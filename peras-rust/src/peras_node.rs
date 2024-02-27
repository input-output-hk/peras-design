use crate::chain::Chain;
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize)]
pub struct InEnvelope {}

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
    inbound: Box<Vec<InEnvelope>>,
    outbound: Box<Vec<OutEnvelope>>,
}

impl Node {
    pub fn new() -> Node {
        println!("starting node");
        Node {
            inbound: Box::new(vec![]),
            outbound: Box::new(vec![]),
        }
    }

    pub fn stop(&self) {
        println!("stopping node")
    }

    pub fn send(&mut self, msg: InEnvelope) {
        self.inbound.push(msg)
    }

    pub fn receive(&mut self) -> Option<OutEnvelope> {
        Some(OutEnvelope::Idle {
            timestamp: Utc::now(),
            source: "N1".to_string(),
            best_chain: Chain {
                blocks: vec![],
                votes: vec![],
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = false;
        assert!(result);
    }
}
