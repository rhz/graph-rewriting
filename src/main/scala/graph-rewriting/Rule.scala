package graph_rewriting

import implicits._

trait Action[N,NL,E<:DiEdgeLike[N],EL]
    extends AbstractArrow[N,NL,E,EL,N,NL,E,EL] {

  type Match = Arrow[N,NL,E,EL,N,NL,E,EL]

  def lhs: Graph[N,NL,E,EL]
  def rhs: Graph[N,NL,E,EL]
  @inline final def dom = lhs
  @inline final def cod = rhs

  /** In-place modification of the codomain of `m`. */
  def apply(m: Match): (Match, Set[N], Set[E])

  def reversed: Action[N,NL,E,EL]

  def transport(m: Match): Match = Arrow(rhs, m.cod,
    m.n collect { case (u, v) if n contains u => (n(u), v) },
    m.e collect { case (x, y) if e contains x => (e(x), y) })
}

sealed abstract class AtomicAction[N,NL,E<:DiEdgeLike[N],EL]
    extends Action[N,NL,E,EL]


case class AddNode[N,NL,E<:DiEdgeLike[N],EL](
  val lhs: Graph[N,NL,E,EL],
  val rhs: Graph[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val nodeRhs: N)(
  implicit val newNode: Graph[N,_,_,_] => N)
    extends AtomicAction[N,NL,E,EL] {
  val label: Option[NL] = rhs(nodeRhs).label
  override def apply(m: Match): (Match, Set[N], Set[E]) = {
    // TODO: When adding a node I should add all edges to/from it as
    // well, but how do I do it with edges between new nodes?
    val n = newNode(m.cod)
    m.cod += n
    for (l <- label) m.cod(n).label = l
    // FIXME: Ugly... it should say transport(m) + (nodeRhs -> n)
    (transport(m) + (nodeRhs, n), Set(n), Set())
  }
  override def reversed = DelNode(rhs, lhs,
    n.inverse, e.inverse, nodeRhs)(newNode)
}

case class DelNode[N,NL,E<:DiEdgeLike[N],EL](
  val lhs: Graph[N,NL,E,EL],
  val rhs: Graph[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val nodeLhs: N)(
  implicit val newNode: Graph[N,_,_,_] => N)
    extends AtomicAction[N,NL,E,EL] {
  override def apply(m: Match): (Match, Set[N], Set[E]) = {
    val n = m(nodeLhs)
    val edges = m.cod(n).edges
    m.cod -= n
    // TODO: Maybe `apply` return a collection.Set instead
    (transport(m), Set(n), edges.toSet)
  }
  override def reversed = AddNode(rhs, lhs,
    n.inverse, e.inverse, nodeLhs)(newNode)
}

case class SetNodeLabel[N,NL,E<:DiEdgeLike[N],EL](
  val lhs: Graph[N,NL,E,EL],
  val rhs: Graph[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val nodeLhs: N)
    extends AtomicAction[N,NL,E,EL] {
  val nodeRhs = n(nodeLhs)
  val label: Option[NL] = rhs(nodeRhs).label
  override def apply(m: Match): (Match, Set[N], Set[E]) = {
    val n = m(nodeLhs)
    label match {
      case Some(l) => m.cod(n).label = l
      case None => m.cod(n).unlabel
    }
    (transport(m), Set(n), Set())
  }
  override def reversed = SetNodeLabel(rhs, lhs,
    n.inverse, e.inverse, nodeRhs)
}


// This is only for edges between old nodes
case class AddEdge[N,NL,E<:DiEdgeLike[N],EL](
  val lhs: Graph[N,NL,E,EL],
  val rhs: Graph[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val edgeRhs: E)(
  implicit val newEdge: (Graph[N,_,E,_], N, N) => E)
    extends AtomicAction[N,NL,E,EL] {
  val ninv = n.inverse
  val sourceRhs: N = edgeRhs.source
  val targetRhs: N = edgeRhs.target
  val sourceLhs: N = ninv(sourceRhs)
  val targetLhs: N = ninv(targetRhs)
  val label: Option[EL] = rhs(edgeRhs).label
  override def apply(m: Match): (Match, Set[N], Set[E]) = {
    // TODO: One way to solve the to/from/bw-new-nodes issue would be
    // to "thread" a map from rhs' nodes to new nodes in the mixture
    val s = m(sourceLhs)
    val t = m(targetLhs)
    val x = newEdge(m.cod, s, t)
    m.cod += x
    for (l <- label) m.cod(x).label = l
    (transport(m) + (edgeRhs, x), Set(s, t), Set(x))
  }
  override def reversed = DelEdge(rhs, lhs, ninv, e.inverse, edgeRhs)
}

case class DelEdge[N,NL,E<:DiEdgeLike[N],EL](
  val lhs: Graph[N,NL,E,EL],
  val rhs: Graph[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val edgeLhs: E)(
  implicit val newEdge: (Graph[N,_,E,_], N, N) => E)
    extends AtomicAction[N,NL,E,EL] {
  override def apply(m: Match): (Match, Set[N], Set[E]) = {
    val x = m(edgeLhs)
    m.cod -= x
    (transport(m), Set(), Set(x))
  }
  override def reversed = AddEdge(rhs, lhs,
    n.inverse, e.inverse, edgeLhs)
}

case class SetEdgeLabel[N,NL,E<:DiEdgeLike[N],EL](
  val lhs: Graph[N,NL,E,EL],
  val rhs: Graph[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val edgeLhs: E)
    extends AtomicAction[N,NL,E,EL] {
  val edgeRhs: E = e(edgeLhs)
  val label: Option[EL] = rhs(edgeRhs).label
  override def apply(m: Match): (Match, Set[N], Set[E]) = {
    val x = m(edgeLhs)
    label match {
      case Some(l) => m.cod(x).label = l
      case None => m.cod(x).unlabel
    }
    (transport(m), Set(), Set(x))
  }
  override def reversed = SetEdgeLabel(rhs, lhs,
    n.inverse, e.inverse, edgeRhs)
}


/*
case class AddEdgeToNewNode[N,NL,E<:DiEdgeLike[N],EL](
  val lhs: Graph[N,NL,E,EL],
  val rhs: Graph[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val edge: E)
    extends AtomicAction[N,NL,E,EL] {
  override def apply(m: Match): (Match, Set[N], Set[E]) = ???
  override def reversed = ???
}

case class AddEdgeFromNewNode[N,NL,E<:DiEdgeLike[N],EL](
  val lhs: Graph[N,NL,E,EL],
  val rhs: Graph[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val edge: E)
    extends AtomicAction[N,NL,E,EL] {
  override def apply(m: Match): (Match, Set[N], Set[E]) = ???
  override def reversed = ???
}
*/


case class Rule[N,NL,E<:DiEdgeLike[N],EL](
  val lhs: Graph[N,NL,E,EL],
  val rhs: Graph[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  var rate: Double = 1.0)(implicit
  val newNode: Graph[N,_,_,_] => N,
  val newEdge: (Graph[N,_,E,_], N, N) => E)
    extends Action[N,NL,E,EL] {

  val actions: Seq[Action[N,NL,E,EL]] = {
    val nimage = n.values.toSet
    val eimage = e.values.toSet
    val addNodes = for (v <- rhs.nodes if !(nimage contains v))
                   yield AddNode(lhs, rhs, n, e, v)
    val delNodes = for (u <- lhs.nodes if !(n contains u))
                   yield DelNode(lhs, rhs, n, e, u)
    val setNodes = for ((u, v) <- n if lhs(u).label != rhs(v).label)
                   yield SetNodeLabel(lhs, rhs, n, e, u)
    val addEdges = for (y <- rhs.edges if !(eimage contains y))
                   yield AddEdge(lhs, rhs, n, e, y)
    val delEdges = for (x <- lhs.edges if !(e contains x))
                   yield DelEdge(lhs, rhs, n, e, x)
    val setEdges = for ((x, y) <- e if lhs(x).label != rhs(y).label)
                   yield SetEdgeLabel(lhs, rhs, n, e, x)
    addNodes.toSeq ++ delNodes ++ setNodes ++ addEdges ++ delEdges ++ setEdges
  }
  def apply(m: Match): (Match, Set[N], Set[E]) =
    actions map (_(m)) reduceLeft ((x, y) => {
      val (cm1, n1, e1) = x
      val (cm2, n2, e2) = y
      (cm1 + cm2, n1 ++ n2, e1 ++ e2)
    })
  def reversed = Rule(rhs, lhs, n.inverse, e.inverse)
}

// TODO: Create a constructor that infers `n` and `e` assuming that
// the interface is a subset of both `lhs` and `rhs`.

