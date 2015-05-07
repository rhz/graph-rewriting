package graph_rewriting

import implicits._

trait Action[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,G]]
    extends Arrow[N,NL,E,EL,N,NL,E,EL,G] {

  // FIXME: Why is this not working?
  // require(!isInjective, "non-injective rule or action: " + this)

  // implicit val ev: G[N,NL,E,EL] <:< Graph[N,NL,E,EL]
  type Match = Arrow[N,NL,E,EL,N,NL,E,EL,G]

  def lhs: G[N,NL,E,EL]
  def rhs: G[N,NL,E,EL]
  @inline final def dom = lhs
  @inline final def cod = rhs

  /** In-place modification of the codomain of `m`. */
  def apply(m: Match, addedNodes: Map[N,N]): (Match, Map[N,N], Set[N], Set[E])
  def apply(m: Match): (Match, Set[N], Set[E]) = {
    val (comatch, _, modNodes, modEdges) = apply(m, Map())
    (comatch, modNodes, modEdges)
  }

  def reversed: Action[N,NL,E,EL,G]

  def transport(m: Match): Match = Arrow(rhs, m.cod,
    m.n collect { case (u, v) if n contains u => (n(u), v) },
    m.e collect { case (x, y) if e contains x => (e(x), y) })

  override def stringPrefix: String = "Action"
}

// --- Atomic actions ---

sealed abstract class AtomicAction[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,G]]//(
  // implicit val ev: G[N,NL,E,EL] <:< Graph[N,NL,E,EL])
    extends Action[N,NL,E,EL,G]


case class AddNode[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,G]](
  val lhs: G[N,NL,E,EL],
  val rhs: G[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val nodeRhs: N)(
  implicit val newNode: G[N,NL,E,EL] => N)
  // override val ev: G[N,NL,E,EL] <:< Graph[N,NL,E,EL])
    extends AtomicAction[N,NL,E,EL,G] {
  val label: Option[NL] = rhs(nodeRhs).label
  def apply(m: Match, addedNodes: Map[N,N])
      : (Match, Map[N,N], Set[N], Set[E]) = {
    val n = newNode(m.cod)
    m.cod += n
    for (l <- label) m.cod(n).label = l
    (transport(m) + (nodeRhs,n),
     addedNodes + (nodeRhs -> n),Set(n),Set())
  }
  // TODO: How can we infer these type parameters?
  def reversed = DelNode(rhs,lhs,n.inverse,e.inverse,nodeRhs)
  override def stringPrefix: String = "AddNode"
}

case class DelNode[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,G]](
  val lhs: G[N,NL,E,EL],
  val rhs: G[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val nodeLhs: N)(
  implicit val newNode: G[N,NL,E,EL] => N)
  // override val ev: G[N,NL,E,EL] <:< Graph[N,NL,E,EL])
    extends AtomicAction[N,NL,E,EL,G] {
  def apply(m: Match, addedNodes: Map[N,N])
      : (Match, Map[N,N], Set[N], Set[E]) = {
    val n = m(nodeLhs)
    val edges = m.cod(n).edges
    m.cod -= n
    // Should `apply` return a collection.Set instead?
    (transport(m),addedNodes,Set(n),edges.toSet)
  }
  def reversed = AddNode(rhs,lhs,n.inverse,e.inverse,nodeLhs)
  override def stringPrefix: String = "DelNode"
}

case class SetNodeLabel[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,G]](
  val lhs: G[N,NL,E,EL],
  val rhs: G[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val nodeLhs: N)//(
  // implicit override val ev: G[N,NL,E,EL] <:< Graph[N,NL,E,EL])
    extends AtomicAction[N,NL,E,EL,G] {
  val nodeRhs = n(nodeLhs)
  val label: Option[NL] = rhs(nodeRhs).label
  def apply(m: Match, addedNodes: Map[N,N])
      : (Match, Map[N,N], Set[N], Set[E]) = {
    val n = m(nodeLhs)
    label match {
      case Some(l) => m.cod(n).label = l
      case None => m.cod(n).unlabel
    }
    (transport(m), addedNodes, Set(n), Set())
  }
  def reversed = SetNodeLabel(rhs,lhs,n.inverse,e.inverse,nodeRhs)
  override def stringPrefix: String = "SetNodeLabel"
}


case class AddEdge[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,G]](
  val lhs: G[N,NL,E,EL],
  val rhs: G[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val edgeRhs: E)(
  implicit val newEdge: (G[N,NL,E,EL],N,N) => E)
  // override val ev: G[N,NL,E,EL] <:< Graph[N,NL,E,EL])
    extends AtomicAction[N,NL,E,EL,G] {
  val ninv = n.inverse
  val sourceRhs: N = edgeRhs.source
  val targetRhs: N = edgeRhs.target
  val label: Option[EL] = rhs(edgeRhs).label
  def inMatch(m1: Match, m2: Map[N,N], n: N) = ninv get n match {
    case Some(u) => m1(u)
    case None => m2 get n match {
      case Some(u) => u
      case None => throw new IllegalArgumentException(
        s"can't find node $n in $m1 nor $m2")
    }
  }
  def apply(m: Match, addedNodes: Map[N,N])
      : (Match, Map[N,N], Set[N], Set[E]) = {
    val s = inMatch(m,addedNodes,sourceRhs)
    val t = inMatch(m,addedNodes,targetRhs)
    val x = newEdge(m.cod,s,t)
    m.cod += x
    for (l <- label) m.cod(x).label = l
    (transport(m) + (edgeRhs, x),addedNodes,Set(s,t),Set(x))
  }
  def reversed = DelEdge(rhs,lhs,ninv,e.inverse,edgeRhs)
  override def stringPrefix: String = "AddEdge"
}

case class DelEdge[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,G]](
  val lhs: G[N,NL,E,EL],
  val rhs: G[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val edgeLhs: E)(
  implicit val newEdge: (G[N,NL,E,EL],N,N) => E)
  // override val ev: G[N,NL,E,EL] <:< Graph[N,NL,E,EL])
    extends AtomicAction[N,NL,E,EL,G] {
  def apply(m: Match, addedNodes: Map[N,N])
      : (Match, Map[N,N], Set[N], Set[E]) = {
    val x = m(edgeLhs)
    m.cod -= x
    (transport(m),addedNodes,Set(),Set(x))
  }
  def reversed = AddEdge(rhs,lhs,n.inverse,e.inverse,edgeLhs)
  override def stringPrefix: String = "DelEdge"
}

case class SetEdgeLabel[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,G]](
  val lhs: G[N,NL,E,EL],
  val rhs: G[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val edgeLhs: E)// (
  // implicit override val ev: G[N,NL,E,EL] <:< Graph[N,NL,E,EL])
    extends AtomicAction[N,NL,E,EL,G] {
  val edgeRhs: E = e(edgeLhs)
  val label: Option[EL] = rhs(edgeRhs).label
  def apply(m: Match, addedNodes: Map[N,N])
      : (Match, Map[N,N], Set[N], Set[E]) = {
    val x = m(edgeLhs)
    label match {
      case Some(l) => m.cod(x).label = l
      case None => m.cod(x).unlabel
    }
    (transport(m), addedNodes, Set(), Set(x))
  }
  def reversed = SetEdgeLabel(rhs,lhs,n.inverse,e.inverse,edgeRhs)
  override def stringPrefix: String = "SetEdgeLabel"
}


// --- Rules ---

case class Rate(val name: String, val value: Double = 1.0) {
  override def toString = name
}

class Rule[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,G]](
  val lhs: G[N,NL,E,EL],
  val rhs: G[N,NL,E,EL],
  val n: Map[N,N],
  val e: Map[E,E],
  val rate: Rate)(
  implicit val newNode: G[N,NL,E,EL] => N,
           val newEdge: (G[N,NL,E,EL],N,N) => E)
  // override val ev: G[N,NL,E,EL] <:< Graph[N,NL,E,EL])
    extends Action[N,NL,E,EL,G] {

  val actions: Seq[Action[N,NL,E,EL,G]] = {
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
  def apply(m: Match, addedNodes: Map[N,N])
      : (Match, Map[N,N], Set[N], Set[E]) =
    actions.foldLeft((Arrow(rhs,m.cod,Map(),Map()),Map.empty[N,N],
      Set.empty[N],Set.empty[E])) ({
        case ((cm1, an1, n1, e1), action) => {
          val (cm2, an2, n2, e2) = action(m, an1)
          (cm1 + cm2, an1 ++ an2, n1 ++ n2, e1 ++ e2)
        }
      })
  def reversed() = Rule(rhs,lhs,n.inverse,e.inverse,Rate(rate.name + "_reversed"))(newNode,newEdge)
  def reversed(rate: Rate) = Rule(rhs,lhs,n.inverse,e.inverse,rate)
  override def stringPrefix: String = "Rule"
}

object Rule {

  // Creates a `Rule` with `n` and `e` given by all common nodes and edges in `lhs` and `rhs`.
  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,G]](
    lhs: G[N,NL,E,EL], rhs: G[N,NL,E,EL], rate: Rate)(implicit
      newNode: G[N,NL,E,EL] => N,
      newEdge: (G[N,NL,E,EL],N,N) => E): Rule[N,NL,E,EL,G] = {
    val n = for (n <- lhs.nodes if rhs.nodes contains n) yield (n,n)
    val e = for (e <- lhs.edges if rhs.edges contains e) yield (e,e)
    new Rule(lhs,rhs,n.toMap,e.toMap,rate)
  }

  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,G]](
    lhs: G[N,NL,E,EL], rhs: G[N,NL,E,EL],
    n: Map[N,N], e: Map[E,E], rate: Rate)(implicit
      newNode: G[N,NL,E,EL] => N,
      newEdge: (G[N,NL,E,EL],N,N) => E): Rule[N,NL,E,EL,G] =
    new Rule(lhs,rhs,n,e,rate)
}

