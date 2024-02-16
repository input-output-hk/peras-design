use crate::parameters::*;
use rand::seq::SliceRandom;
use rand::Rng;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

#[derive(Debug, Eq, Clone, Hash, PartialEq)]
#[allow(non_snake_case)]
pub struct NodeId {
    nodeId: String,
}

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.nodeId)
    }
}

impl<'a> Deserialize<'a> for NodeId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'a>,
    {
        Ok(NodeId {
            nodeId: String::deserialize(deserializer)?,
        })
    }
}

impl Serialize for NodeId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.nodeId)
    }
}

#[allow(non_snake_case)]
pub fn MkNodeId(node_id: &str) -> NodeId {
    NodeId {
        nodeId: String::from(node_id),
    }
}

#[derive(Debug, Deserialize, Serialize)]
pub struct Topology {
    connections: HashMap<NodeId, HashSet<NodeId>>,
}

impl Topology {
    pub fn empty() -> Topology {
        Topology {
            connections: HashMap::new(),
        }
    }
}

fn set_singleton<T: Eq + Hash>(item: T) -> HashSet<T> {
    let mut set = HashSet::new();
    set.insert(item);
    set
}

// FIXME: Consider revising memory allocation.
pub fn connect_node(upstream: &NodeId, downstream: &NodeId, topology: &mut Topology) {
    topology
        .connections
        .entry(upstream.clone())
        .and_modify(|v| {
            v.insert(downstream.clone());
        })
        .or_insert(set_singleton(downstream.clone()));
}

pub fn random_topology(rng: &mut impl Rng, parameters: &Parameters) -> Topology {
    let mut topology = Topology::empty();
    let node_ids: Vec<NodeId> = (1..=parameters.peerCount)
        .map(|i| NodeId {
            nodeId: format!("N{}", i),
        })
        .collect();
    fn random_connect(
        r: &mut impl Rng,
        upstream: &NodeId,
        downstreams: Vec<NodeId>,
        m: usize,
        t: &mut Topology,
    ) {
        let mut candidates = downstreams.clone();
        candidates.retain(|x| x != upstream);
        let chosen = candidates.choose_multiple(r, m);
        chosen.for_each(|downstream| connect_node(upstream, downstream, t));
    }
    node_ids.iter().for_each(|upstream| {
        random_connect(
            rng,
            upstream,
            node_ids.clone(),
            parameters.downstreamCount,
            &mut topology,
        )
    });
    topology
}
