#include "common.h"

/*
  Rebuild every edge of the graph.

  A node's own adjacency is derived from its assign trees, but each edge also
  has to be recorded on the node at the far end. Workers therefore fill their
  own slice directly and hand the far-end updates to the worker that owns the
  target, so no node is ever written by two workers at once. Ownership is taken
  from the node id, which is stable, and AdjSet sorts on read, so the result
  does not depend on how the work was divided.
*/
void graph::reconnectAll() {
  std::vector<Node*> nodes;
  nodes.reserve(countNodes());
  for (SuperNode* super : sortedSuper) {
    for (Node* member : super->member) nodes.push_back(member);
  }
  const ptrdiff_t nodeNum = nodes.size();
  const int buckets = omp_get_max_threads();

  #pragma omp parallel for schedule(static)
  for (ptrdiff_t i = 0; i < nodeNum; i ++) nodes[i]->clear_relation();

  std::vector<std::vector<std::vector<PendingEdge>>> pending(
      buckets, std::vector<std::vector<PendingEdge>>(buckets));

  #pragma omp parallel
  {
    std::vector<std::vector<PendingEdge>>& mine = pending[omp_get_thread_num()];
    std::vector<PendingEdge> local;
    #pragma omp for schedule(static)
    for (ptrdiff_t i = 0; i < nodeNum; i ++) {
      local.clear();
      nodes[i]->updateConnect(&local);
      for (const PendingEdge& edge : local) mine[edge.target->id % buckets].push_back(edge);
    }
  }

  /* one bucket per worker, so each node is written by a single thread */
  #pragma omp parallel for schedule(static)
  for (int owner = 0; owner < buckets; owner ++) {
    for (int worker = 0; worker < buckets; worker ++) {
      for (const PendingEdge& edge : pending[worker][owner]) {
        if (edge.isNext) edge.target->addNext(edge.value);
        else edge.target->addPrev(edge.value);
      }
    }
  }

  connectDep();
  reconnectSuper();
}

void graph::connectDep() {
  for (SuperNode* super : sortedSuper) {
    for (Node* member : super->member) {
      if (member->type == NODE_REG_SRC) member->updateDep();
    }
  }
}

void graph::reconnectSuper() {
  for (SuperNode* super : sortedSuper) {
    super->clear_relation();
  }
  for (SuperNode* super : sortedSuper) {
    for (Node* member : super->member) member->constructSuperConnect();
  }
}

void graph::removeNodesNoConnect(NodeStatus status) {
  if (globalConfig.LogLevel > 1) {
    for (SuperNode* super : sortedSuper) {
      for (Node* n : super->member) {
        if (n->status == status) {
          fprintf(stderr, "[RemoveNodes] remove status=%d name=%s type=%d super=%d\n",
                  status, n->name.c_str(), n->type, super->id);
        }
      }
    }
  }
  for (SuperNode* super : sortedSuper) {
    super->member.erase(
      std::remove_if(super->member.begin(), super->member.end(), [status](const Node* n){ return n->status == status; }),
      super->member.end()
    );
  }
  removeEmptySuper();
}

size_t graph::countNodes() {
  size_t ret = 0;
  for (SuperNode* super : sortedSuper) ret += super->member.size();
  return ret;
}

void graph::removeNodes(NodeStatus status) {
  removeNodesNoConnect(status);
  removeEmptySuper();
  reconnectSuper();
}

void graph::removeEmptySuper() {
  sortedSuper.erase(
    std::remove_if(sortedSuper.begin(), sortedSuper.end(), [](const SuperNode* super) {return (super->superType == SUPER_VALID || super->superType == SUPER_UPDATE_REG) && super->member.size() == 0; }),
    sortedSuper.end()
  );
}

void graph::orderAllNodes() {
  int order = 1;
  for (size_t i = 0; i < sortedSuper.size(); i ++) {
    sortedSuper[i]->order = i;
    for (size_t j = 0; j < sortedSuper[i]->member.size(); j ++) {
      sortedSuper[i]->member[j]->orderInSuper = j;
      sortedSuper[i]->member[j]->order = order ++;
    }
  }
}
