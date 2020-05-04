package hz.ricardo
package graph_rewriting

import scala.annotation.tailrec
import scala.collection.mutable
import scala.language.higherKinds  // TODO: necessary?

// Without this import 'Set' defaults to
// scala.collection.immutable.Set rather than scala.collection.Set
// (i.e. the common super-class of mutable and immutable sets).
//
// In the graph classes below, we're using mutable sets to store nodes
// and edges, so it would seem logic to just import
// scala.collection.mutable.Set and make that the default.  However,
// mutable.Map.keySet returns a collection.Set and thus Node.edges has
// to be of this type.  Then the line adjacency(n)(e) = (e.nodes - n)
// forces adjacency to be of type
// mutable.Map[N,mutable.Map[E,collection.Set[N]]] and so it
// propagates everywhere.  Consequently, we're using the unspecific
// scala.collection.Set as the the default.
import scala.collection.Set

import utils._

/**
 * The abstract base class of all graphs.
 *
 * @tparam N the type of nodes in this graph
 * @tparam NL the type of node labels in this graph
 * @tparam E the type of edges in this graph
 * @tparam EL the type of edge labels in this graph
 */
abstract class BaseGraph[N, NL, E <: EdgeLike[N], EL] {
  graph =>

  type This <: BaseGraph[N, NL, E, EL]

  def empty: This
  def asThis: This

  def copy: This = {
    val g = empty
    g.addNodes(nodes)
    g.addEdges(edges)
    for ((n,l) <- nodelabels) g(n).label = l
    for ((e,l) <- edgelabels) g(e).label = l
    g
  }

  def isEmpty: Boolean = nodes.isEmpty

  // --- Nodes and edges ---

  val nodes = mutable.Set.empty[N]
  val edges = mutable.Set.empty[E]
  val nodelabels = mutable.Map.empty[N, NL]
  val edgelabels = mutable.Map.empty[E,EL]
  val adjacency = mutable.Map.empty[N,mutable.Map[E,Set[N]]]

  // - Accessing inner nodes and edges -

  class Node(n: N) {
    @inline def value: N = n
    @inline def label: Option[NL] = nodelabels get n
    @inline def label_= (l: NL) = nodelabels(n) = l
    @inline def isLabelled: Boolean = nodelabels isDefinedAt n
    @inline def unlabel: Unit = nodelabels -= n
    type Other = BaseGraph[_,_,_,_]
    def matches(that: Other#Node) =
      !this.isLabelled || (that.isLabelled && this.label == that.label)
    def edges: Set[E] = adjacency(n).keySet
    def edgesWith(m: N): Iterable[E] =
      adjacency(n) withFilter (_._2 contains m) map (_._1)
    def degree: Int = adjacency(n).size
    def neighbours: Set[N] = adjacency(n).values.flatten.toSet
    // Q: Should I have this or just use adjacency directly?
    // def edgesAndNeighbours: Map[E,Set[N]] = adjacency(n)
  }

  class Edge(e: E) {
    @inline def value: E = e
    @inline def label: Option[EL] = edgelabels get e
    @inline def label_= (l: EL) = edgelabels(e) = l
    @inline def isLabelled: Boolean = edgelabels isDefinedAt e
    @inline def unlabel: Unit = edgelabels -= e
    @inline def nodes: Set[N] = e.nodes
    def adjacents: Set[E] =
      for (n <- e.nodes; f <- graph(n).edges if e != f) yield f
    type Other = BaseGraph[_,_,_,_]
    def matches(that: Other#Edge) =
      !this.isLabelled || (that.isLabelled && this.label == that.label)
  }

  def apply(n: N) = if (nodes contains n) new Node(n)
                    else throw new NoSuchElementException(
                      "no such node " + n + " in graph " + this)
  def apply(e: E) = if (edges contains e) new Edge(e)
                    else throw new NoSuchElementException(
                      "no such edge " + e + " in graph " + this)

  // - Adding/removing nodes and edges one by one -

  def += (n: N): this.type = {
    if (nodes add n)
      adjacency(n) = mutable.Map.empty[E, Set[N]]
    this
  }
  def += (e: E): this.type = {
    edges += e
    for (n <- e.nodes) {
      this += n
      adjacency(n)(e) = (e.nodes - n)
    }
    this
  }
  def += (g: BaseGraph[N,NL,E,EL]): this.type = {
    addNodes(g.nodes)
    addEdges(g.edges)
    for ((n, l) <- g.nodelabels) nodelabels(n) = l
    for ((e, l) <- g.edgelabels) edgelabels(e) = l
    this
  }
  def + (n: N): This = copy += n
  def + (e: E): This = copy += e
  def + (g: BaseGraph[N,NL,E,EL]): This = copy += g

  def -= (n: N): this.type = {
    if (nodes contains n) {
      for ((e, ms) <- adjacency(n)) {
        edges -= e
        for (m <- ms) adjacency(m) -= e
      }
      adjacency -= n
      nodes -= n
      nodelabels -= n
    }
    this
  }
  def -= (e: E): this.type = {
    if (edges contains e) {
      edges -= e
      edgelabels -= e
      for (n <- e.nodes)
        adjacency(n) -= e
    }
    this
  }
  def -= (g: BaseGraph[N,NL,E,EL]): this.type = {
    delNodes(g.nodes)
    delEdges(g.edges)
    this
  }

  // - Adding/removing nodes and edges in bulk -

  def addNodes(ns: Traversable[N]): this.type = {
    for (n <- ns) this += n
    this
  }
  def addNodes(n: N, ns: N*): this.type = {
    this += n
    for (n <- ns) this += n
    this
  }
  def addEdges(es: Traversable[E]): this.type = {
    for (e <- es) this += e
    this
  }
  def addEdges(e: E, es: E*): this.type = {
    this += e
    for (e <- es) this += e
    this
  }

  def delNodes(ns: Traversable[N]): this.type = {
    for (n <- ns) this -= n
    this
  }
  def delNodes(n: N, ns: N*): this.type = {
    this -= n
    for (n <- ns) this -= n
    this
  }
  def delEdges(es: Traversable[E]): this.type = {
    for (e <- es) this -= e
    this
  }
  def delEdges(e: E, es: E*): this.type = {
    this -= e
    for (e <- es) this -= e
    this
  }


  // --- Subgraphs ---

  /** Test whether this graph is a subgraph of `that`. */
  def subgraphOf(that: BaseGraph[N,NL,E,EL]): Boolean =
    nodes.forall(n => (that.nodes contains n) && (
      if (nodelabels isDefinedAt n)
        (that.nodelabels isDefinedAt n) &&
        (nodelabels(n) == that.nodelabels(n))
      else true)) &&
    edges.forall(e => (that.edges contains e) && (
      if (edgelabels isDefinedAt e)
        (that.edgelabels isDefinedAt e) &&
        (edgelabels(e) == that.edgelabels(e))
      else true))

  // - Disjoint set systems -

  /** Find root of node `n` in (possibly partially constructed) tree
    * represented by the `parent` map.
    */
  def findRoot(n: N, parent: Map[N,N]): (N,Map[N,N]) =
    if (parent(n) == n) (n,parent)
    else {
      val (m,p) = findRoot(parent(n),parent)
      (m,p + (n -> m))
    }

  /** Disjoint set union. */
  def disjunion(n: N, m: N, parent: Map[N,N]): Map[N,N] = {
    val (x,p1) = findRoot(n,parent)
    val (y,p2) = findRoot(m,p1)
    if (x == y) p2
    else p2 + (x -> y)
  }

  /** Returns map from each node in this graph to its parent node in
    * the tree representing its disjoint set (ie connected component).
    */
  def parents: Map[N,N] =
    edges.foldLeft((nodes,nodes).zipped.toMap)({
      case (parent,e) => {
        val n = e.nodes.head
        e.nodes.tail.foldLeft(parent)({
          case (parent,m) => disjunion(n,m,parent) })
      }
    })

  /** Returns map from roots of each disjoint set to the set of nodes
    * in the set.
    */
  def disjointsByRoot: Map[N,Set[N]] = {
    val ps = parents
    ps.foldLeft((ps,
      Map.empty[N,Set[N]] withDefaultValue Set.empty[N]))({
        case ((parents,disjs),(n,p)) => {
          val (root,ps) = findRoot(p,parents)
          (ps, disjs + (root -> (disjs(root) + n)))
        }
      })._2
  }

  /** Collection of disjoint sets in this graph. */
  def disjoints: Iterable[Set[N]] = disjointsByRoot.values

  /** `true` if this graph is connected. */
  def isConnected: Boolean = disjointsByRoot.size == 1

  /** Returns the collection of connected components as separate graphs. */
  def components: Iterable[This] =
    for (ns <- disjoints) yield inducedSubgraph(ns)

  /** Constructs an induced subgraph of this graph given the set of nodes `ns`. */
  def inducedSubgraph(ns: Set[N]): This = {
    val g = empty
    for (n <- ns) {
      g += n
      if (nodelabels isDefinedAt n)
        g(n).label = nodelabels(n)
    }
    for (e <- edges if e.nodes forall (ns contains _)) {
      g += e
      if (edgelabels isDefinedAt e)
        g(e).label = edgelabels(e)
    }
    g
  }

  def inducedSubgraph(n: N, ns: N*): This =
    inducedSubgraph(Set(n) ++ ns)


  // --- Equality ---

  /** Graph equality. */
  def sameAs(that: This): Boolean =
    (this subgraphOf that) && (that subgraphOf this)

  def canEqual(other: Any) = other match {
    case _: BaseGraph[_,_,_,_] => true
    case _ => false
  }

  override def equals(other: Any): Boolean = other match {
    case that: BaseGraph[_,_,_,_] =>
      (that canEqual this) &&
      (this.nodes == that.nodes) &&
      (this.edges == that.edges) &&
      (this.nodelabels == that.nodelabels) &&
      (this.edgelabels == that.edgelabels)
    case _ => false
  }

  override def hashCode: Int =
    41 * (
      41 * (
        41 * (
          41 + nodes.hashCode
        ) + edges.hashCode
      ) + nodelabels.hashCode
    ) + edgelabels.hashCode

  def stringPrefix = "Graph"
  override def toString = s"$stringPrefix(" +
    s"nodes = $nodes, edges = $edges" +
    (if (nodelabels.nonEmpty) s", nodelabels = $nodelabels" else "") +
    (if (edgelabels.nonEmpty) s", edgelabels = $edgelabels" else "") + ")"
}

/**
 * Simple graphs.
 *
 * @tparam N the type of nodes in this graph
 * @tparam NL the type of node labels in this graph
 * @tparam E the type of edges in this graph
 * @tparam EL the type of edge labels in this graph
 */
class Graph[N, NL, E <: EdgeLike[N], EL] extends BaseGraph[N, NL, E, EL] {
  type This = Graph[N, NL, E, EL]
  def empty = new Graph[N, NL, E, EL]
  def asThis = this
}

object Graph {

  // --- Constructors ---

  private def const[N,NL,E<:EdgeLike[N],EL](
    nodes: Traversable[(N,Option[NL])],
    edges: Traversable[(E,Option[EL])]): Graph[N,NL,E,EL] = {
    val g = new Graph[N,NL,E,EL]
    g.addNodes(nodes map (_._1))
    g.addEdges(edges map (_._1))
    for ((n,Some(l)) <- nodes) g(n).label = l
    for ((e,Some(l)) <- edges) g(e).label = l
    g
  }

  implicit def empty[N,NL,E<:EdgeLike[N],EL] = new Graph[N,NL,E,EL]

  class GraphConstructorWithNodes[N,NL](
    nodes: Traversable[(N,Option[NL])]) {
    def apply[E<:EdgeLike[N],EL](edges: (E,Option[EL])*) =
      const(nodes, edges)
    def apply() = const[N,NL,IdDiEdge[Int,N],String](nodes, List())
  }

  def apply[N,NL](n1: (N,Option[NL]), nodes: (N,Option[NL])*) =
    new GraphConstructorWithNodes[N,NL](n1 +: nodes)

  class GraphConstructor[N,NL,E<:EdgeLike[N],EL] {
    def apply(nodes: (N,Option[NL])*)(edges: (E,Option[EL])*)
        : Graph[N,NL,E,EL] = Graph.const(nodes,edges)
    def apply(nodes: Iterable[N], edges: Iterable[E])
        : Graph[N,NL,E,EL] =
      const[N,NL,E,EL](nodes zip Stream.continually(None),
                       edges zip Stream.continually(None))
    def empty: Graph[N,NL,E,EL] = new Graph[N,NL,E,EL]
  }

  def withType[N,NL,E<:EdgeLike[N],EL] =
    new GraphConstructor[N,NL,E,EL]
}
