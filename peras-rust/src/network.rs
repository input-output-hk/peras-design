use std::thread::JoinHandle;

use peras_topology::{network::Topology, parameters::Parameters};
use rand::rngs::StdRng;

use crate::{chain::Chain, message::Message, peras_node::NodeHandle};

pub struct Network {
    topology: Topology,
    parameters: Parameters,
    seed: StdRng,
    nodes: Vec<NodeHandle>,
}

impl Network {
    pub(crate) fn new(topology: &Topology, parameters: &Parameters, seed: u64) -> Network {
        todo!()
    }

    pub(crate) fn start(&self) -> NetworkHandle {
        todo!()
    }
}

pub struct NetworkHandle {
    thread: Option<JoinHandle<()>>,
}

impl NetworkHandle {
    pub(crate) fn stop(&self) {
        todo!()
    }

    pub(crate) fn broadcast(&self, msg: Message) {
        todo!()
    }

    pub(crate) fn get_preferred_chain(&self, node_id: &str) -> Chain {
        todo!()
    }
}
