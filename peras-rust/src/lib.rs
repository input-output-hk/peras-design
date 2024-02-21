pub struct PerasNode {
    node_id: String,
    stake: f64,
}

/// Create a new Peras node
///
#[no_mangle]
pub unsafe extern "C" fn start_node(_node_id: *const char, _node_stake: f64) -> *mut PerasNode {
    panic!("not implemented")
}

#[no_mangle]
pub unsafe extern "C" fn stop_node(_node: *mut PerasNode) {
    panic!("not implemented")
}

#[no_mangle]
pub unsafe extern "C" fn send_message(_node: *mut PerasNode, _buf: *const u8, _len: usize) {
    panic!("not implemented")
}

#[no_mangle]
pub unsafe extern "C" fn receive_message(
    _node: *mut PerasNode,
    _buf: *mut u8,
    _len: usize,
) -> usize {
    panic!("not implemented")
}
