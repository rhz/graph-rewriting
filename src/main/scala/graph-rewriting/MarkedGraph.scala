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

  type G[Y,Z<:E,W] <: BaseMarkedDiGraph[N,Y,Z,W]
  override def stringPrefix = "MarkedDiGraph"

  override def copy = {
    val g = super.copy
    for (n <- markedNodes) g(n).mark
    g
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

  // We might want to override this method and addEdges
  // to disallow the creation of edges at marked nodes.
  // override def += (e: E): this.type = ???

  import DiGraph.{Unifier,EdgeUnifier}

  // NOTE: Again we have the problem here that H needs to be a subtype
  // of BaseMarkedDiGraph instead of BaseDiGraph, but that would make
  // the overriden type of `intersections` incompatible (I actually
  // haven't checked yet but I should... maybe there's no problem).
  /*
  override def intersections[N2,E2<:DiEdgeLike[N2],N3,E3<:DiEdgeLike[N3],
    H[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    that: H[N2,NL,E2,EL])(implicit
      nodeUnifier: Unifier[N,N2,N3],
      // TODO: Probably I should make edgeUnifier a (H[N3,NL,E3,EL],Map[N,N3],Map[N2,N3]) => Unifier instead of EdgeUnifier
      edgeUnifier: EdgeUnifier[N,N2,N3,E,E2,E3],
      graphBuilder: () => H[N3,NL,E3,EL],
      ev: This <:< H[N,NL,E,EL])
      : Seq[(H[N3,NL,E3,EL],
             Arrow[N3,NL,E3,EL,N ,NL,E ,EL,H],
             Arrow[N3,NL,E3,EL,N2,NL,E2,EL,H])] =
    for {
      (pb,f1:Arrow[N3,NL,E3,EL,N ,NL,E ,EL,H],f2:Arrow[N3,NL,E3,EL,N2,NL,E2,EL,H]) <-
        super.intersections(that)(nodeUnifier,edgeUnifier,graphBuilder,ev)
      pbM: MarkedDiGraph[N3,NL,E3,EL] = MarkedDiGraph(pb)
      if (pbM.nodes forall (n =>
        (this(f1(n)).marked, that(f2(n)).marked) match {
          case (false,false) => true
          case (true,true) => {
            pbM(n).mark // add mark
            val d = pbM(n).degree
            (d == this(f1(n)).degree) && (d == that(f2(n)).degree)
          }
          case (true,false) => {
            pbM(n).mark // add mark
            val d = pbM(n).degree
            (d == this(f1(n)).degree)
          }
          case (false,true) => {
            pbM(n).mark // add mark
            val d = pbM(n).degree
            (d == that(f2(n)).degree)
          }
        }))} yield (pbM,Arrow[N3,NL,E3,EL,N ,NL,E ,EL,H](pbM,this.asThis,f1.n,f1.e),
                        Arrow[N3,NL,E3,EL,N2,NL,E2,EL,H](pbM,that,f2.n,f2.e))
  */

  override def toString = s"$stringPrefix(nodes = " + (nodes map (
    n => if (markedNodes contains n) n else "*" + n + "*")) +
    ", edges = $edges" +
    (if (nodelabels.nonEmpty) s", nodelabels = $nodelabels" else "") +
    (if (edgelabels.nonEmpty) s", edgelabels = $edgelabels" else "") + ")"
}

class MarkedDiGraph[N,NL,E<:DiEdgeLike[N],EL]
    extends BaseMarkedDiGraph[N,NL,E,EL] {
       // with ConcreteDiGraph[N,NL,E,EL,MarkedDiGraph] {
  type G[Y,Z<:E,W] = MarkedDiGraph[N,Y,Z,W]
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
    for ((n, Some(l)) <- nodes) g(n).label = l
    for ((e, Some(l)) <- edges) g(e).label = l
    g
  }

  def empty[N,NL,E<:DiEdgeLike[N],EL] = new MarkedDiGraph[N,NL,E,EL] // = const(List(), List())

  def apply[N,NL](n1: (N,Option[NL]), nodes: (N,Option[NL])*) = new {
    def apply[E<:DiEdgeLike[N],EL](edges: (E,Option[EL])*) =
      const(n1 +: nodes, edges)
    def apply() = const[N,NL,IdDiEdge[Int,N],String](n1 +: nodes, List())
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
      const(nodes, edges)
  }
}

