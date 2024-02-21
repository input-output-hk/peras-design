#ifndef PERAS_H
#define PERAS_H

#include <unistd.h>

// opaque type of handle to the underlying Rust node
typedef struct ForeignNode ForeignNode;

// Start node, returning a point to its handle
ForeignNode* start_node(const char *nodeId, const double stake);


// Stop a running node
void stop_node(ForeignNode* node);

// Send a message of given length to the node
void send_message(ForeignNode* node, const char* buf, const size_t len);

// Receive a message of maximum given length from the node
// This might be blocking.
// Returns the actual length of the message stored in buf
int receive_message(ForeignNode* node, char* buf, const size_t max_size);

#endif
