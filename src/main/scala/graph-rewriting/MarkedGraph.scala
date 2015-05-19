package graph_rewriting

// This is needed because mutable.Map.keySet returns a collection.Set
// and thus Node.edges has to be of this type.  Then the line
// adjacency(n)(e) = (e.nodes - n) forces adjacency to be of type
// mutable.Map[N, mutable.Map[E, collection.Set[N]]] and so it
// propagates everywhere.
import scala.collection.Set
import scala.collection.mutable

import utils._
import implicits._


abstract class BaseMarkedDiGraph[N,NL,E<:DiEdgeLike[N],EL]
    extends BaseDiGraph[N,NL,E,EL] {

  // type G[Y,Z<:E,W] <: BaseMarkedDiGraph[N,Y,Z,W]
  override def stringPrefix = "MarkedDiGraph"

  // FIXME: This is a hack to work around the issue with type G that can't
  // be given an upper bound here or it won't mix with ConcreteDiGraph
  override def copy =
    super.copy match {
      case g: BaseMarkedDiGraph[N,NL,E,EL] => {
        // for (n <- markedNodes) g(n).mark
        for (n <- inMarks) g(n).inMark
        for (n <- outMarks) g(n).outMark
        g.asInstanceOf[This] // since copy returned a BaseMarkedDiGraph, this is safe
      }
      case g => g
    }

  val markedNodes = mutable.Set.empty[N] // subset of nodes

  class MarkedNode(n: N) extends DiNode(n) {
    def marked: Boolean = markedNodes contains n
    def mark = { markedNodes += n; this }
    def unmark = { markedNodes -= n; this }
  }

  override def apply(n: N): MarkedNode =
    if (nodes contains n) new MarkedNode(n)
    else throw new NoSuchElementException(
      "no such node " + n + " in graph " + this)

  def mark(n: N, ns: N*): this.type = {
    require(nodes contains n, s"node $n not in graph $this")
    markedNodes += n
    for (n <- ns) {
      require(nodes contains n, s"node $n not in graph $this")
      markedNodes += n
    }
    this
  }
  def mark(ns: Traversable[N]): this.type = {
    for (n <- ns) {
      require(nodes contains n, s"node $n not in graph $this")
      markedNodes += n
    }
    this
  }

  // We might want to override this method and addEdges
  // to disallow the creation of edges at marked nodes.
  // override def += (e: E): this.type = ???

  override def -= (n: N): this.type = {
    super.-=(n)
    if (markedNodes contains n) markedNodes -= n
    this
  }

  override def connectedIso(that: BaseDiGraph[N,NL,E,EL]): Boolean =
    that match {
      case thatM: BaseMarkedDiGraph[_,_,_,_] =>
        (this eq that) ||
        ((this.nodes.size == that.nodes.size) &&
         (this.edges.size == that.edges.size) && {
           val f = findBijection(that)
           f.isDefined && (
             (markedNodes map f.get.n) == thatM.markedNodes)
         })
      case _ => super.connectedIso(that)
    }

  // TODO: Fix this mess (is it really a mess?)...
  // Maybe H should be <: G or something
  override def intersections[N2,E2<:DiEdgeLike[N2],N3,E3<:DiEdgeLike[N3],
    H[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    that: H[N2,NL,E2,EL])(implicit
      nodeUnifier: Unifier[N,N2,N3],
      edgeUnifier: (H[N3,NL,E3,EL],Map[N,N3],Map[N2,N3]) => Unifier[E,E2,E3],
      graphBuilder: () => H[N3,NL,E3,EL],
      ev: This <:< H[N,NL,E,EL])
      : Seq[(H[N3,NL,E3,EL],
             Arrow[N3,NL,E3,EL,N ,NL,E ,EL,H],
             Arrow[N3,NL,E3,EL,N2,NL,E2,EL,H])] = that match {
    case thatM: BaseMarkedDiGraph[N2,NL,E2,EL] => // H <: BaseMarkedDiGraph
      for {
        // TODO: Why the type inference doesn't work?
        (pb,f1,f2) <- super.intersections[N2,E2,N3,E3,H](that) // (nodeUnifier,edgeUnifier,graphBuilder,ev)
        pbM = pb.asInstanceOf[BaseMarkedDiGraph[N3,NL,E3,EL]] // since H <: BaseMarkedDiGraph this should just be an upcast
        if (pbM.nodes forall (n =>
          (this(f1(n)).marked, thatM(f2(n)).marked) match {
            case (false,false) => true
            case (true,true) => {
              pbM(n).mark // add mark
              val d = pbM(n).degree
                (d == this(f1(n)).degree) && (d == thatM(f2(n)).degree)
            }
            case (true,false) => {
              pbM(n).mark // add mark
              val d = pbM(n).degree
              (d == this(f1(n)).degree)
            }
            case (false,true) => {
              pbM(n).mark // add mark
              val d = pbM(n).degree
              (d == thatM(f2(n)).degree)
            }
          }))
        pbH = pbM.asInstanceOf[H[N3,NL,E3,EL]] // and here we downcast pb back to what it actually is
      } yield (pbH, Arrow[N3,NL,E3,EL,N ,NL,E ,EL,H](pbH,this.asThis,f1.n,f1.e),
                    Arrow[N3,NL,E3,EL,N2,NL,E2,EL,H](pbH,that,f2.n,f2.e))
    case _ => super.intersections(that)
  }

  override def unions[N2,E2<:DiEdgeLike[N2],N3,E3<:DiEdgeLike[N3],
    H[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    that: H[N2,NL,E2,EL])(implicit
      nodeUnifier: Unifier[N,N2,N3],
      edgeUnifier: (H[N3,NL,E3,EL],Map[N,N3],Map[N2,N3]) => Unifier[E,E2,E3],
      graphBuilder: () => H[N3,NL,E3,EL],
      ev: This <:< H[N,NL,E,EL])
      : Seq[(H[N3,NL,E3,EL],
             Arrow[N ,NL,E ,EL,N3,NL,E3,EL,H],
             Arrow[N2,NL,E2,EL,N3,NL,E3,EL,H])] = that match {
    case thatM: BaseMarkedDiGraph[N2,NL,E2,EL] => // H <: BaseMarkedDiGraph
      for ((po,f1,f2) <- super.unions(that)(
        nodeUnifier,edgeUnifier,graphBuilder,ev)) yield {
        val poM = po.asInstanceOf[BaseMarkedDiGraph[N3,NL,E3,EL]] // since H <: BaseMarkedDiGraph this should just be an upcast
        for (n <- poM.nodes if f1.n.exists({ case (u,v) =>
          v == n && this(u).marked }) || f2.n.exists({ case (u,v) =>
          v == n && thatM(u).marked }))
          poM(n).mark // add mark
        val poH = poM.asInstanceOf[H[N3,NL,E3,EL]]
        (poH, Arrow[N ,NL,E ,EL,N3,NL,E3,EL,H](this.asThis,poH,f1.n,f1.e),
              Arrow[N2,NL,E2,EL,N3,NL,E3,EL,H](that,poH,f2.n,f2.e))
      }
    case _ => super.unions(that)
  }

  override def toString = s"$stringPrefix(nodes = " + (nodes map (
    n => if (markedNodes contains n) "*" + n + "*" else n)) +
    s", edges = $edges" +
    (if (nodelabels.nonEmpty) s", nodelabels = $nodelabels" else "") +
    (if (edgelabels.nonEmpty) s", edgelabels = $edgelabels" else "") + ")"

  override def toString[M](nm: Map[N,M]) = {
    val em = (for (e <- edges) yield
      (e, e.copy(nm(e.source), nm(e.target)))).toMap
    val nl = for ((n,l) <- nodelabels) yield (nm(n),l)
    val el = for ((e,l) <- edgelabels) yield (em(e),l)
    s"$stringPrefix(" +
      "nodes = Set(" + (nm map { case (u,v) =>
        if (markedNodes contains u) "*" + v + "*" else v }).mkString(", ") + "), " +
      "edges = Set(" + em.values.mkString(", ") + ")" +
      (if (nl.nonEmpty) s", nodelabels = $nl" else "") +
      (if (el.nonEmpty) s", edgelabels = $el" else "") + ")"
  }
}

// trait ConcreteMarkedDiGraph[N,NL,E<:DiEdgeLike[N],EL,
//   H[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,H]]
//     extends BaseMarkedDiGraph[N,NL,E,EL]
//        with ConcreteDiGraph[N,NL,E,EL,H]

class MarkedDiGraph[N,NL,E<:DiEdgeLike[N],EL]
    extends BaseMarkedDiGraph[N,NL,E,EL] // {
       with ConcreteDiGraph[N,NL,E,EL,MarkedDiGraph] {
  // type G[Y,Z<:E,W] = MarkedDiGraph[N,Y,Z,W]
  def empty = new MarkedDiGraph[N,NL,E,EL]
  def asThis = this
}

object MarkedDiGraph {

  // TODO: Most of this could also be abstracted away into a GraphCompanion

  // --- Constructors ---

  private def const[N,NL,E<:DiEdgeLike[N],EL](
    nodes: Traversable[(N,Option[NL])],
    edges: Traversable[(E,Option[EL])]): MarkedDiGraph[N,NL,E,EL] = {
    val g = new MarkedDiGraph[N,NL,E,EL]
    g.addNodes(nodes map (_._1))
    g.addEdges(edges map (_._1))
    for ((n,Some(l)) <- nodes) g(n).label = l
    for ((e,Some(l)) <- edges) g(e).label = l
    g
  }

  implicit def empty[N,NL,E<:DiEdgeLike[N],EL]() =
    new MarkedDiGraph[N,NL,E,EL]

  def apply[N,NL](n1: (N,Option[NL]), nodes: (N,Option[NL])*) = new {
    def apply[E<:DiEdgeLike[N],EL](edges: (E,Option[EL])*) =
      const(n1 +: nodes,edges)
    def apply() = const[N,NL,IdDiEdge[Int,N],String](n1 +: nodes,List())
  }

  // TODO: This should be available for Graphs and DiGraphs as well,
  // it's pretty generic conceptually: from another type of graph
  // construct this type of graph.
  def apply[N,NL,E<:DiEdgeLike[N],EL](g: BaseGraph[N,NL,E,EL])
      : MarkedDiGraph[N,NL,E,EL] = g match {
    case g: MarkedDiGraph[_,_,_,_] => g
    case _ => {
      val mg = new MarkedDiGraph[N,NL,E,EL]
      mg.addNodes(g.nodes)
      mg.addEdges(g.edges)
      for ((n,l) <- g.nodelabels) mg(n).label = l
      for ((e,l) <- g.edgelabels) mg(e).label = l
      mg
    }
  }

  def withType[N,NL,E<:DiEdgeLike[N],EL] = new {
    def apply(nodes: (N,Option[NL])*)(edges: (E,Option[EL])*) =
      const(nodes,edges)
    def apply(nodes: Iterable[N], edges: Iterable[E]) =
      const[N,NL,E,EL](nodes zip Stream.continually(None),
                       edges zip Stream.continually(None))
  }
}

