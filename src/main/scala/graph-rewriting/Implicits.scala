package graph_rewriting

object implicits {

  // -- Edges --
  final implicit class DiEdgeConst[N](n1: N) {
    def ~> (n2: N) = DiEdge(n1, n2)
  }
}

