/*
  Adjacency container with std::set<T*> semantics backed by a vector.

  reconnectAll rebuilds every edge from scratch after almost every pass, so the
  dominant pattern is bulk append followed by read-only iteration. Appending and
  deduplicating once on first read removes the tree node that std::set allocates
  per edge.

  Iteration yields neighbours in ascending id order. The replaced std::set<T*>
  ordered by address, which made anything derived from neighbour order depend
  on the allocation pattern rather than on the input.

  Storage is contiguous, so an insert may move the elements. A loop over one
  direction must not insert into or erase from that same container. Graph code
  walks one direction while rewriting the opposite one, which respects this.
*/

#ifndef ADJACENCY_H
#define ADJACENCY_H

#include <algorithm>
#include <vector>

template <typename T>
class AdjSet {
 public:
  typedef typename std::vector<T*>::const_iterator const_iterator;

  void insert(T* elem) {
    elems.push_back(elem);
    sorted = false;
  }
  template <typename Iter>
  void insert(Iter first, Iter last) {
    if (first == last) return;
    elems.insert(elems.end(), first, last);
    sorted = false;
  }
  void erase(T* elem) {
    normalize();
    const_iterator iter = locate(elem);
    if (iter != elems.end()) elems.erase(iter);
  }
  void clear() {
    elems.clear();
    sorted = true;
  }
  size_t size() const { normalize(); return elems.size(); }
  bool empty() const { normalize(); return elems.empty(); }
  const_iterator begin() const { normalize(); return elems.begin(); }
  const_iterator end() const { normalize(); return elems.end(); }
  const_iterator find(T* elem) const { normalize(); return locate(elem); }

 private:
  mutable std::vector<T*> elems;
  mutable bool sorted = true;

  /* sort by id and deduplicate, restoring the set view of the elements */
  void normalize() const {
    if (sorted) return;
    std::sort(elems.begin(), elems.end(), byId);
    elems.erase(std::unique(elems.begin(), elems.end()), elems.end());
    sorted = true;
  }
  const_iterator locate(T* elem) const {
    const_iterator iter = std::lower_bound(elems.begin(), elems.end(), elem, byId);
    return (iter != elems.end() && *iter == elem) ? iter : elems.end();
  }
  static bool byId(const T* a, const T* b) { return a->id < b->id; }
};

#endif
