package graph_rewriting

object implicits {

  // -- Nodes --
  def next(xs: Traversable[Int]) = if (xs.isEmpty) 0 else (xs.max + 1)

  implicit def newIntNode(g: Graph[Int,_,_,_]): Int = next(g.nodes)

  implicit def newStringNode(g: Graph[String,_,_,_]): String = {
    val id = util.Random.nextString(10)
    if (g.nodes contains id) newStringNode(g)
    else id
  }

  // -- Edges --
  final implicit class DiEdgeConst[N](n1: N) {
    def ~> (n2: N) = DiEdge(n1, n2)
  }

  implicit def newIdDiEdge[N](g: Graph[N,_,IdDiEdge[Int,N],_],
    u: N, v: N) = new IdDiEdge(next(g(u) outgoingTo v map {
      case IdDiEdge(id,_,_) => id }), u, v)

  // -- Maps --
  final implicit class InvertibleMap[A,B](m: Map[A,B]) {
    def inverse = m map (_.swap)
  }

}

