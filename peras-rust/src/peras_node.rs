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
