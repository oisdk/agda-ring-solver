# Performance

* General note: the vast majority of the performance gains come from maintaining
  syntactic equality (*not* from the sparse optimizations, unlike in the Coq
  solver!). Anyone looking to understand that should check out the
  relevant section of the report.
* There's about a ~3 second oerhead over the old solver (on small problems). Why
  is this?

# Step-By-Step

* I think the step-by-step solutions could be improved by using A* (the
  heuristic can be "size of expression") or dijkstra's or something on the
  generated relation, because we can skip sections of the relation. Here's the
  question: do we always skip just one section? Or do we skip more?

# Reflection

* We could probably give more arguments to the reflection interface.
