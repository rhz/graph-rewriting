package graph_rewriting

import utils.Counter

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

  implicit class IdDiEdgeConst[N](n1: N) {
    def ~~> (n2: N) = IdDiEdge(Counter.next, n1, n2)
  }

  implicit def newIdDiEdge[N](g: Graph[N,_,IdDiEdge[Int,N],_],
    u: N, v: N) = new IdDiEdge(next(g(u) outgoingTo v map {
      case IdDiEdge(id,_,_) => id }), u, v)

  // -- Maps --
  final implicit class InvertibleMap[A,B](m: Map[A,B]) {
    def inverse = m map (_.swap)
  }

  // -- Polynomials --
  implicit def numToMn[N,NL,E<:DiEdgeLike[N],EL](n: Double) =
    Mn[N,NL,E,EL](n)
  implicit def graphToMn[N,NL,E<:DiEdgeLike[N],EL](
    g: Graph[N,NL,E,EL]) = Mn[N,NL,E,EL](g)
  // implicit def numToPn[N,NL,E<:DiEdgeLike[N],EL](n: Double) =
  //   Pn[N,NL,E,EL](Mn[N,NL,E,EL](n))
  // implicit def graphToPn[N,NL,E<:DiEdgeLike[N],EL](
  //   g: Graph[N,NL,E,EL]) = Pn[N,NL,E,EL](Mn(g))
  implicit def mnToPn[N,NL,E<:DiEdgeLike[N],EL](m: Mn[N,NL,E,EL]) =
    Pn[N,NL,E,EL](m)

  // -- Eqs --
  implicit def eqsToEqs[N,NL,E<:DiEdgeLike[N],EL](
    eqs: Traversable[Eq[N,NL,E,EL]]) = new Eqs(eqs)
}

