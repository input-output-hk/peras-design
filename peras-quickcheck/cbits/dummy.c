#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include "peras.h"

struct ForeignNode {
  char *nodeId;
  double stake;
};

// Start node, returning a point to its handle
ForeignNode* start_node(const char *nodeId,const double stake) {
  ForeignNode *node = malloc(sizeof(ForeignNode));
  size_t len = strlen(nodeId);

  node->stake = stake;
  node->nodeId = malloc(len + 1);

  strlcpy(node->nodeId, nodeId, len);

  return node;
}


// Stop a running node
void stop_node(ForeignNode* node) {
  if(!node) return;

  free(node->nodeId);
  free(node);
}
