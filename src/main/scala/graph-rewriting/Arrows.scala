package graph_rewriting

// TODO: Make arrows for undirected graphs.

class PInj[N1,E1<:DiEdgeLike[N1],
           N2,E2<:DiEdgeLike[N2]](
  val n: Map[N1, N2],
  val e: Map[E1, E2]) {

  def inverse = new PInj(n map (_.swap), e map (_.swap))

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
  def isTotal(dom: Graph[N1,_,E1,_]): Boolean =
    dom.nodes.forall(n isDefinedAt _) &&
    dom.edges.forall(e isDefinedAt _)

  def apply(u: N1): N2 = n(u)
  def apply(x: E1): E2 = e(x)

  def stringPrefix: String = "PInj"
  override def toString = stringPrefix + "(" + (n mkString ", ") +
    (if (n.nonEmpty && e.nonEmpty) ", " + (e mkString ", ") + ")"
     else ")")
}

