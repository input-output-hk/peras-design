mod block;
mod chain;
mod crypto;
mod event;
mod message;
mod peras_node;

use std::{
    cmp,
    ffi::{c_char, CStr},
    slice,
};

use peras_node::{InEnvelope, Node, NodeHandle, NodeParameters};

/// For testing purpose, must be at the toplevel
#[cfg(test)]
extern crate quickcheck_macros;

/// Opaque representation of a Peras node for foreign use
pub struct PerasNode {
    handle: Box<NodeHandle>,
}

/// Creates and starts a new Peras node
///
#[no_mangle]
pub unsafe extern "C" fn start_node(
    node_id: *const c_char,
    node_stake: u64,
    total_stake: u64,
) -> Box<PerasNode> {
    let node_id = CStr::from_ptr(node_id).to_str().unwrap().into();
    let node: Node = Node::new(
        node_id,
        NodeParameters {
            node_stake,
            total_stake,
            ..Default::default()
        },
    );
    let handle = node.start();
    Box::new(PerasNode {
        handle: Box::new(handle),
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
    match serde_json::from_slice(bytes) {
        Ok(msg) => node.handle.send(msg),
        Err(err) => println!(
            "Failed to deserialise message: {}\nError: {}",
            std::str::from_utf8(bytes).unwrap(),
            err
        ),
    }
}

#[no_mangle]
pub unsafe extern "C" fn receive_message(node: &mut PerasNode, buf: *mut u8, len: usize) -> usize {
    let msg = node.handle.receive();
    let bytes = serde_json::to_vec(&msg).unwrap();
    let bytes_ptr = bytes.as_ptr();
    let count_copy = cmp::min(len, bytes.len());

    unsafe {
        std::ptr::copy(bytes_ptr, buf, count_copy);
        count_copy
    }
}
