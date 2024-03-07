use std::{
    collections::{HashMap, HashSet},
    thread::JoinHandle,
    time::Duration,
};

use netsim::{Bandwidth, HasBytesSize, NodePolicy, SimConfiguration, SimContext, SimSocket};
use peras_topology::{
    network::{NodeId, Topology},
    parameters::Parameters,
};
use rand::{rngs::StdRng, Rng, SeedableRng};

use crate::{
    chain::Chain,
    message::Message,
    peras_node::{Node, NodeHandle, NodeParameters, ProtocolParameters},
};

type Ctx = netsim::SimContext<Message>;

impl HasBytesSize for Message {
    fn bytes_size(&self) -> u64 {
        // FIXME this is lame...
        serde_json::to_vec(self).unwrap().len().try_into().unwrap()
    }
}

pub struct NodeInterface {
    /// The node's state
    node: Node,
    /// The node's handle, if it is running
    node_handle: Option<NodeHandle>,
    /// The socket for sending and receiving messages
    edges: SimSocket<Message>,
}

pub struct Network {
    topology: Topology,
    parameters: Parameters,
    seed: StdRng,
    context: Ctx,
    nodes: HashMap<NodeId, NodeInterface>,
}

impl Network {
    pub fn new(topology: &Topology, parameters: &Parameters) -> Network {
        // configure the network simulation
        let configuration = SimConfiguration::default();

        // create the network context from which we can create "sockets"
        let mut context: Ctx = SimContext::with_config(configuration);

        // default protocol parameters
        let protocol = ProtocolParameters::default();

        let mut seed = StdRng::seed_from_u64(parameters.randomSeed);

        let nodes = topology
            .connections
            .iter()
            .map(|(nodeId, _)| {
                let iface = make_node(
                    &nodeId.nodeId,
                    &mut context,
                    &topology.connections.get(nodeId).unwrap(),
                    parameters,
                    &protocol,
                    &mut seed,
                );
                (nodeId.clone(), iface)
            })
            .collect();

        Network {
            topology: topology.clone(),
            parameters: parameters.clone(),
            seed,
            context,
            nodes,
        }
    }

    pub fn start(&self) -> NetworkHandle {
        todo!()
    }
}

fn make_node(
    node_id: &String,
    context: &mut Ctx,
    edges: &HashSet<NodeId>,
    parameters: &Parameters,
    protocol: &ProtocolParameters,
    seed: &mut StdRng,
) -> NodeInterface {
    let socket = context.open().unwrap();
    context.set_node_policy(
        socket.id(),
        NodePolicy {
            bandwidth_down: Bandwidth::bits_per(u64::MAX, Duration::from_secs(1)),
            bandwidth_up: Bandwidth::bits_per(u64::MAX, Duration::from_secs(1)),
        },
    );

    let node_stake = seed.gen_range(0..parameters.maximumStake);

    let node_params = NodeParameters {
        node_stake,
        protocol_parameters: protocol.clone(),
    };

    let node = Node::new(node_id.to_string(), node_params);

    NodeInterface {
        node,
        node_handle: None,
        edges: socket,
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
