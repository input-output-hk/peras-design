use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
    thread::{self, JoinHandle},
    time::Duration,
};

use netsim::{
    Bandwidth, HasBytesSize, NodePolicy, SimConfiguration, SimContext, SimId, SimSocket, TryRecv,
};
use peras_topology::{
    network::{NodeId, Topology},
    parameters::Parameters,
};
use rand::{rngs::StdRng, Rng, SeedableRng};

use crate::{
    chain::{empty_chain, Chain},
    event::UniqueId,
    message::{Message, OutMessage},
    peras_node::{InEnvelope, Node, NodeHandle, NodeParameters, OutEnvelope, ProtocolParameters},
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
    dispatcher: Option<JoinHandle<()>>,
    /// The socket for sending and receiving messages
    socket: Arc<Mutex<SimSocket<Message>>>,
    /// The socket's id
    socket_id: SimId,
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
        let mut threads = self
            .nodes
            .iter()
            .map(|(node_id, iface)| {
                let mut node_handle = iface.node.start(self.parameters.maximumStake);
                let socket = Arc::clone(&iface.socket);
                let node_id_1 = node_id.clone();
                let downstreams = self
                    .topology
                    .connections
                    .get(&node_id_1)
                    .unwrap()
                    .iter()
                    .map(|(nid, n)| self.nodes.get(nid).unwrap().socket_id.clone())
                    .collect();
                // start dispatching thread for each node
                thread::spawn(move || {
                    receive_and_forward_loop(node_id_1, socket, downstreams, &mut node_handle)
                })
            })
            .collect::<Vec<_>>();
        // can't mutate the NodeInterface while iterating at the same
        // time iterator would need to be mutable and we need to borrow it again
        // to retrieve all downstream peers
        for (_, iface) in self.nodes.iter_mut() {
            iface.dispatcher = Some(threads.pop().unwrap());
        }
    }

    pub(crate) fn stop(&mut self) {
        // stop all nodes in then network
        // for (_, iface) in self.nodes.iter_mut() {
        //     if let Some(handle) = &mut iface.node_handle {
        //         handle.stop();
        //     }
        // }
    }

    pub(crate) fn broadcast(&self, msg: Message) {
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

fn receive_and_forward_loop(
    node_id: NodeId,
    sim_socket: Arc<Mutex<SimSocket<Message>>>,
    downstreams: Vec<SimId>,
    node_handle: &mut NodeHandle,
) {
    let mut no_msg_count = 0;
    loop {
        thread::sleep(Duration::from_millis(no_msg_count));
        let mut socket = sim_socket.lock().unwrap();
        // handle messages that are sent to the node from the network
        match socket.try_recv() {
            TryRecv::Some((from, msg)) => {
                no_msg_count = 0;
                node_handle.send(InEnvelope::SendMessage {
                    origin: None,
                    in_id: UniqueId::new(&msg),
                    in_message: msg,
                });
            }
            TryRecv::NoMsg => {
                if no_msg_count < 10 {
                    no_msg_count += 1;
                };
                continue;
            }
            TryRecv::Disconnected => {
                break;
            }
        }
        // pull messages from the node and send them to the network
        while let Some(envelope) = node_handle.try_receive() {
            match envelope {
                OutEnvelope::SendMessage {
                    out_message,
                    timestamp: _,
                    source: _,
                    destination: _,
                    bytes: _,
                    out_id: _,
                } => {
                    downstreams.iter().for_each(|id| {
                        socket
                            .send_to(*id, out_message.clone())
                            .expect("send failed");
                    });
                }
                OutEnvelope::Idle {
                    timestamp: _,
                    source: _,
                    best_chain,
                } => {
                    node_handle.current_best_chain = best_chain;
                }
                _ => {}
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
        dispatcher: None,
        socket: Arc::clone(&socket_mutex),
        socket_id,
    }
}
