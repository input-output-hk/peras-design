mod peras_node;

use std::{
    ffi::{c_char, CStr},
    slice,
};

use peras_node::{InEnvelope, Node};

/// Opaque representation of a Peras node for foreign use
pub struct PerasNode {
    nodeId: String,
    stake: f64,
    handle: Box<Node>,
}

/// Create a new Peras node
///
#[no_mangle]
pub unsafe extern "C" fn start_node(node_id: *const c_char, node_stake: f64) -> Box<PerasNode> {
    let node: Node = Node::new();
    Box::new(PerasNode {
        nodeId: CStr::from_ptr(node_id).to_str().unwrap().into(),
        stake: node_stake,
        handle: Box::new(node),
    })
}

#[no_mangle]
pub unsafe extern "C" fn stop_node(node: &mut PerasNode) {
    node.handle.stop()
}

#[no_mangle]
pub unsafe extern "C" fn send_message(node: &mut PerasNode, buf: *const u8, len: usize) {
    // make a slice
    let bytes = slice::from_raw_parts(buf, len);
    // unmarshall message
    let msg: InEnvelope = serde_json::from_slice(bytes).unwrap();
    node.handle.send(msg);
}

#[no_mangle]
pub unsafe extern "C" fn receive_message(node: &mut PerasNode, buf: *mut u8, _len: usize) -> usize {
    match node.handle.receive() {
        Node => 0,
        Some(msg) => {
            let bytes = serde_json::to_vec(&msg).unwrap();
            let bytes_ptr = bytes.as_ptr();

            unsafe {
                for i in 0..bytes.len() {
                    buf.write(*bytes_ptr);
                    *bytes_ptr.add(i);
                }
                bytes.len()
            }
        }
    }
}
