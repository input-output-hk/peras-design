#ifndef PERAS_H
#define PERAS_H

// opaque type of handle to the underlying Rust node
typedef struct ForeignNode ForeignNode;

// Start node, returning a point to its handle
ForeignNode* start_node(const char *nodeId, const double stake);


// Stop a running node
void stop_node(ForeignNode* node);

#endif
