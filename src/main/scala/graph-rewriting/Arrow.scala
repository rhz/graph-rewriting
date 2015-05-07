package graph_rewriting

import implicits._

/** Partial graph homomorphism. */
abstract class Arrow[
  N1,NL1,E1<:DiEdgeLike[N1],EL1,
  N2,NL2,E2<:DiEdgeLike[N2],EL2,
  G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]] { //(implicit
    // ev1: G[N1,NL1,E1,EL1] <:< Graph[N1,NL1,E1,EL1],
    // ev2: G[N2,NL2,E2,EL2] <:< Graph[N2,NL2,E2,EL2]) {

  def dom: G[N1,NL1,E1,EL1]
  def cod: G[N2,NL2,E2,EL2]
  def n: Map[N1,N2]
  def e: Map[E1,E2]

  def inverse = Arrow(cod, dom, n.inverse, e.inverse)

  /** Check if this arrow is injective. */
  def isInjective: Boolean =
    n.values.toSeq.combinations(2).forall { case Seq(n1,n2) => n1 != n2 } &&
    e.values.toSeq.combinations(2).forall { case Seq(e1,e2) => e1 != e2 }

  /** Check if this arrow is structure-preserving. */
  def isHomomorphic: Boolean =
    e.keys.forall(x => // if its source and target are defined in `n`
     !(n.isDefinedAt(x.source) && n.isDefinedAt(x.target)) ||
      (n(x.source) == e(x).source) && (n(x.target) == e(x).target)) // the square has to commute

  /** Check if this arrow is total. */
  def isTotal: Boolean =
    dom.nodes.forall(n isDefinedAt _) &&
    dom.edges.forall(e isDefinedAt _)

  def apply(u: N1): N2 = n(u)
  def apply(x: E1): E2 = e(x)

  def + (u: N1, v: N2) = Arrow(dom,cod,n + (u -> v),e)
  def + (x: E1, y: E2) = Arrow(dom,cod,n,e + (x -> y))
  def + (that: Arrow[N1,NL1,E1,EL1,N2,NL2,E2,EL2,G]) = {
    require(dom == that.dom, "incompatible domains")
    require(cod == that.cod, "incompatible codomains")
    require(that.n forall { case (u,v) =>
      !(n contains u) || (v == n(u)) }, "incompatible node map")
    require(that.e forall { case (x,y) =>
      !(e contains x) || (y == e(x)) }, "incompatible edge map")
    Arrow(dom,cod,n ++ that.n,e ++ that.e)
  }

  def stringPrefix: String = "Arrow"
  override def toString = stringPrefix + "(" + n.mkString(", ") +
    (if (n.nonEmpty && e.nonEmpty) ", " + e.mkString(", ") + ")" else ")")
}

object Arrow {

  def apply[N1,NL1,E1<:DiEdgeLike[N1],EL1,
            N2,NL2,E2<:DiEdgeLike[N2],EL2,
            G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    from: G[N1,NL1,E1,EL1],
    to: G[N2,NL2,E2,EL2],
    nodeMap: Map[N1,N2],
    edgeMap: Map[E1,E2]) = //(implicit
      // ev1: G[N1,NL1,E1,EL1] <:< Graph[N1,NL1,E1,EL1],
      // ev2: G[N2,NL2,E2,EL2] <:< Graph[N2,NL2,E2,EL2]) =
    new Arrow[N1,NL1,E1,EL1,N2,NL2,E2,EL2,G] {
      def dom = from
      def cod = to
      def n = nodeMap
      def e = edgeMap
    }
}

