package graph_rewriting

import scala.reflect.ClassTag
import implicits._

// TODO: Make arrows for undirected graphs.

abstract class AbstractArrow[
  N1,NL1,E1<:DiEdgeLike[N1],EL1,
  N2,NL2,E2<:DiEdgeLike[N2],EL2] {

  def dom: Graph[N1,NL1,E1,EL1]
  def cod: Graph[N2,NL2,E2,EL2]
  def n: Map[N1,N2]
  def e: Map[E1,E2]

  def inverse: AbstractArrow[N2,NL2,E2,EL2,N1,NL1,E1,EL1] =
    Arrow(cod, dom, n.inverse, e.inverse)

  /** Check if this arrow is injective. */
  def isInjective: Boolean =
    n.values.toSeq.combinations(2).forall { case Seq(n1, n2) => n1 != n2 } &&
    e.values.toSeq.combinations(2).forall { case Seq(e1, e2) => e1 != e2 }

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

  // def +(u: N1, v: N2): AbstractArrow[N1,NL1,E1,EL1,N2,NL2,E2,EL2]
  // def +(uv: (N1, N2)): AbstractArrow[N1,NL1,E1,EL1,N2,NL2,E2,EL2]
  // def +(x: E1, y: E2): AbstractArrow[N1,NL1,E1,EL1,N2,NL2,E2,EL2]
  // def +(xy: (E1, E2)): AbstractArrow[N1,NL1,E1,EL1,N2,NL2,E2,EL2]

  def stringPrefix: String = "AbstractArrow"
  override def toString = stringPrefix + "(" + (n mkString ", ") +
    (if (n.nonEmpty && e.nonEmpty) ", " + (e mkString ", ") + ")"
     else ")")
}

case class Arrow[N1,NL1,E1<:DiEdgeLike[N1],EL1,
                 N2,NL2,E2<:DiEdgeLike[N2],EL2](
  val dom: Graph[N1,NL1,E1,EL1],
  val cod: Graph[N2,NL2,E2,EL2],
  val n: Map[N1,N2],
  val e: Map[E1,E2])
    extends AbstractArrow[N1,NL1,E1,EL1,N2,NL2,E2,EL2] {

  override def stringPrefix: String = "Arrow"

  def + (u: N1, v: N2) = Arrow(dom, cod, n + (u -> v), e)
  def + (x: E1, y: E2) = Arrow(dom, cod, n, e + (x -> y))
  // def + (uv: (N1, N2)) = Arrow(dom, cod, n + uv, e)
  // def + (xy: (E1, E2)) = Arrow(dom, cod, n, e + xy)

  def + [X1,X2](kv: (X1, X2))(implicit ev1: ClassTag[X1],
    ev2: ClassTag[X2], ev3: ClassTag[N1], ev4: ClassTag[N2],
    ev5: ClassTag[E1], ev6: ClassTag[E2]) = kv match {
    case (u: N1, v: N2) => Arrow(dom, cod, n + (u -> v), e)
    case (x: E1, y: E2) => Arrow(dom, cod, n, e + (x -> y))
  }

  def + (other: Arrow[N1,NL1,E1,EL1,N2,NL2,E2,EL2]) = {
    require(dom == other.dom, "incompatible domains")
    require(cod == other.cod, "incompatible codomains")
    require(other.n forall { case (u, v) =>
      !(n contains u) || (v == n(u)) }, "incompatible node map")
    require(other.e forall { case (x, y) =>
      !(e contains x) || (y == e(x)) }, "incompatible edge map")
    Arrow(dom, cod, n ++ other.n, e ++ other.e)
  }
}

