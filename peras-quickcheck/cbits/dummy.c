#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include "peras.h"

struct ForeignNode {
  char *nodeId;
  double stake;
};

static char buffer[4096];
static size_t buffer_length;

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


// store message from node
void send_message(ForeignNode* node, const char* buf, const size_t len) {
  memcpy(buffer, buf, len);
  buffer_length = len;
}



// deliver back message
int receive_message(ForeignNode* node, char *buf, const size_t max_len) {
  memcpy(buf, buffer, buffer_length);
  return buffer_length;
}
