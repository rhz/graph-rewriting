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
    u: N, v: N) = new IdDiEdge(next(g(u) edgesTo v map {
      case IdDiEdge(id,_,_) => id }), u, v)

  // -- Maps --
  final implicit class InvertibleMap[A,B](m: Map[A,B]) {
    def inverse = m map (_.swap)
  }

  // -- Rate monomials and polynomials --
  implicit def nameToRate(name: String) = Rate(name)
  // By not implicitly converting to RateMn we can use RatePn.* method
  // implicit def nameToRMn(name: String) = RateMn(Rate(name))
  // implicit def rateToRMn(k: Rate) = RateMn(k)
  implicit def nameToRPn(name: String) = RatePn(RateMn(Rate(name)))
  implicit def rateToRPn(k: Rate) = RatePn(RateMn(k))
  implicit def rateMnToRPn(rm: RateMn) = RatePn(rm)

  // -- Graph monomials and polynomials --
  // Rates don't have required type information
  // implicit def nameToMn(name: String) = Mn(name)
  // implicit def nameToPn(name: String) = Pn(Mn(name))
  // implicit def rateToMn(k: Rate) = Mn(k)
  // implicit def rateToPn(k: Rate) = Pn(Mn(k))
  // implicit def rateMnToMn(rm: RateMn) = Mn(rm)
  // implicit def rateMnToPn(rm: RateMn) = Pn(Mn(rm))
  // implicit def ratePnToMn(rp: RatePn) = Mn(rp)
  // implicit def ratePnToPn(rp: RatePn) = Pn(Mn(rp))
  implicit def graphToMn[N,NL,E<:DiEdgeLike[N],EL](
    g: Graph[N,NL,E,EL]): Mn[N,NL,E,EL] = Mn(g)
  implicit def graphToPn[N,NL,E<:DiEdgeLike[N],EL](
    g: Graph[N,NL,E,EL]) = Pn[N,NL,E,EL](Mn(g))
  implicit def mnToPn[N,NL,E<:DiEdgeLike[N],EL](m: Mn[N,NL,E,EL]) =
    Pn[N,NL,E,EL](m)

  // -- Graph --
  implicit def withLabel[T,U](x: (T,U)) = (x._1, Some(x._2))
  implicit def withoutLabel[T,U](x: T): (T, Option[U])  = (x, None)
  implicit def toSome[T](x: T) = Some(x)
}

