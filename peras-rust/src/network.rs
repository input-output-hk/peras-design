use std::{
    collections::{HashMap, HashSet},
    sync::{Arc, Mutex},
    thread::{self, JoinHandle},
    time::Duration,
};

use netsim::{Bandwidth, HasBytesSize, NodePolicy, SimConfiguration, SimContext, SimSocket};
use peras_topology::{
    network::{NodeId, Topology},
    parameters::Parameters,
};
use rand::{rngs::StdRng, Rng, SeedableRng};

use crate::{
    chain::{empty_chain, Chain},
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
    socket: Arc<Mutex<SimSocket<Message>>>,
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

    pub fn start(&mut self) {
        // start all nodes
        for (node_id, iface) in self.nodes.iter_mut() {
            let node_handle = iface.node.start(self.parameters.maximumStake);
            iface.node_handle = Some(node_handle);
            let socket = Arc::clone(&iface.socket);
            let node_id_1 = node_id.clone();
            // start dispatching thread for each node
            let receiver = thread::spawn(move || receive_and_forward_loop(node_id_1, socket));
        }
    }

    pub(crate) fn stop(&mut self) {
        // stop all nodes in then network
        for (_, iface) in self.nodes.iter_mut() {
            if let Some(handle) = &mut iface.node_handle {
                handle.stop();
            }
        }
    }

    pub(crate) fn broadcast(&self, msg: Message) {
        println!("Broadcasting message: {:?}", msg);
        // broadcast the message to all nodes in the network
        // we trick the node into thinking it's receiving a message from the network
        // by sending it to itself
        for (_, iface) in self.nodes.iter() {
            let sock = iface.socket.lock().unwrap();
            sock.send_to(sock.id(), msg.clone()).expect("send failed");
        }
    }

    pub(crate) fn get_preferred_chain(&self, node_id: &str) -> Chain {
        empty_chain()
    }
}

fn receive_and_forward_loop(node_id: NodeId, sim_socket: Arc<Mutex<SimSocket<Message>>>) {
    let mut no_msg_count = 0;
    loop {
        thread::sleep(Duration::from_millis(no_msg_count));
        let mut socket = sim_socket.lock().unwrap();
        match socket.try_recv() {
            netsim::TryRecv::Some((from, msg)) => {
                no_msg_count = 0;
                println!(
                    "Node {} received message from {}: {:?}",
                    node_id.nodeId, from, msg
                );
            }
            netsim::TryRecv::NoMsg => {
                if no_msg_count < 10 {
                    no_msg_count += 1;
                };
                continue;
            }
            netsim::TryRecv::Disconnected => {
                break;
            }
        }
    }
}

fn make_node(
    node_id: &String,
    context: &mut Ctx,
    parameters: &Parameters,
    protocol: &ProtocolParameters,
    seed: &mut StdRng,
) -> NodeInterface {
    let socket = context.open().unwrap();
    let socket_id = socket.id();
    let socket_mutex = Arc::new(Mutex::new(socket));
    context.set_node_policy(
        socket_id,
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
        socket: Arc::clone(&socket_mutex),
    }
}
