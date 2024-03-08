use std::ffi::{c_char, CStr};

use crate::network::Network;

/// Creates and starts a new Peras network
///
/// Creates a new network with the given topology and parameters and starts it.
/// The seed is used to initialize the random number generator.
#[no_mangle]
pub unsafe extern "C" fn start_network(
    topology: *const c_char,
    parameters: *const c_char,
) -> Box<Network> {
    let topo_str = CStr::from_ptr(topology).to_str().unwrap().into();
    let topology = serde_json::from_str(topo_str).unwrap();
    let params_str = CStr::from_ptr(parameters).to_str().unwrap().into();
    let parameters = serde_json::from_str(params_str).unwrap();
    let mut network: Network = Network::new(&topology, &parameters);
    network.start();
    Box::new(network)
}

/// Stops the given Peras network
#[no_mangle]
pub unsafe extern "C" fn stop_network(network: &mut Network) {
    network.stop()
}

/// Broadcasts a message to all nodes in the network
#[no_mangle]
pub unsafe extern "C" fn broadcast(network: &mut Network, buf: *const u8, len: usize) {
    // make a slice
    let bytes = std::slice::from_raw_parts(buf, len);
    // unmarshall message
    match serde_json::from_slice(bytes) {
        Ok(msg) => network.broadcast(msg),
        Err(err) => println!(
            "Failed to deserialise message: {}\nError: {}",
            std::str::from_utf8(bytes).unwrap(),
            err
        ),
    }
}

/// Return the current preferred chain for given node
///
/// The JSON representation of the chain is written to the given buffer and
/// the number of bytes written is returned.
///
/// If the buffer is too small, the function returns the required buffer size.
#[no_mangle]
pub unsafe extern "C" fn get_preferred_chain(
    network: &mut Network,
    node_id: *const c_char,
    buf: *mut u8,
    len: usize,
) -> usize {
    let node_id = CStr::from_ptr(node_id).to_str().unwrap().into();
    let chain = network.get_preferred_chain(node_id);
    let chain_bytes = serde_json::to_vec(&chain).unwrap();
    let size = chain_bytes.len();
    if len < size {
        return size;
    }
    unsafe {
        std::ptr::copy(chain_bytes.as_ptr(), buf, size);
        size
    }
}
