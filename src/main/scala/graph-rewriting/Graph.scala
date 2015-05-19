package graph_rewriting

import scala.annotation.tailrec
import scala.collection.mutable

// This is needed because mutable.Map.keySet returns a collection.Set
// and thus Node.edges has to be of this type.  Then the line
// adjacency(n)(e) = (e.nodes - n) forces adjacency to be of type
// mutable.Map[N,mutable.Map[E,collection.Set[N]]] and so it
// propagates everywhere.
import scala.collection.Set

import utils._
import implicits._

abstract class BaseGraph[N,NL,E<:EdgeLike[N],EL] {
  graph =>

  // type EdgeUpperBound >: E <: EdgeLike[N]
  // type EdgeUpperBound[X] <: EdgeLike[X]
  // type G[X,Y,Z<:EdgeLike[X],W] <: BaseGraph[X,Y,Z,W]
  type G[Y,Z<:E,W] <: BaseGraph[N,Y,Z,W]
  type This = G[NL,E,EL]
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
  val nodelabels = mutable.Map.empty[N,NL]
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

trait ConcreteGraph[N,NL,E<:EdgeLike[N],EL,
  H[X,Y,Z<:EdgeLike[X],W] <: ConcreteGraph[X,Y,Z,W,H]]
    extends BaseGraph[N,NL,E,EL] {
  // type G[X,Y,Z<:EdgeLike[X],W] = H[X,Y,Z,W]
  // type EdgeUpperBound[X] = EdgeLike[X]
  // type G[X,Y,Z<:EdgeUpperBound[X],W] = H[X,Y,Z,W]
  type G[Y,Z<:E,W] = H[N,Y,Z,W]
}

class Graph[N,NL,E<:EdgeLike[N],EL]
    extends BaseGraph[N,NL,E,EL]
       with ConcreteGraph[N,NL,E,EL,Graph] {
  def empty = new Graph[N,NL,E,EL]
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

  // TODO: Probably should make this an implicit so that a graphBuilder
  // can be implicitly created for any Graph, would that work?
  def empty[N,NL,E<:EdgeLike[N],EL] = new Graph[N,NL,E,EL] // = const(List(), List())

  def apply[N,NL](n1: (N,Option[NL]), nodes: (N,Option[NL])*) = new {
    def apply[E<:EdgeLike[N],EL](edges: (E,Option[EL])*) =
      const(n1 +: nodes, edges)
    def apply() = const[N,NL,IdDiEdge[Int,N],String](n1 +: nodes, List())
  }

  def withType[N,NL,E<:EdgeLike[N],EL] = new {
    def apply(nodes: (N,Option[NL])*)(edges: (E,Option[EL])*) =
      const(nodes, edges)
  }
}

abstract class BaseDiGraph[N,NL,E<:DiEdgeLike[N],EL]
    extends BaseGraph[N,NL,E,EL] {

  override def stringPrefix = "DiGraph"
  // type EdgeUpperBound >: E <: DiEdgeLike[N]
  // type EdgeUpperBound[X] <: DiEdgeLike[X]
  // type G[X,Y,Z<:EdgeUpperBound[X],W] <: BaseDiGraph[X,Y,Z,W]
  // type G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]
  type G[Y,Z<:E,W] <: BaseDiGraph[N,Y,Z,W]

  class DiNode(n: N) extends Node(n) {
    def outgoing: Set[E] = edges filter (_.source == n)
    def incoming: Set[E] = edges filter (_.target == n)
    def edgesTo(m: N): Set[E] = edges filter (e =>
      e.source == n && e.target == m)
    def edgesFrom(m: N): Set[E] = edges filter (e =>
      e.source == m && e.target == n)
    def inDegree: Int = incoming.size
    def outDegree: Int = outgoing.size
    // TODO: Should this be somewhere else?
    // It should not really be necessary
    def opp(e: E): N =
      if      (e.source == n) e.target
      else if (e.target == n) e.source
      else throw new IllegalArgumentException("node " + n +
        " is not the source nor the target of edge " + e)
  }

  override def apply(n: N): DiNode =
    if (nodes contains n) new DiNode(n)
    else throw new NoSuchElementException(
      "no such node " + n + " in graph " + this)


  // --- Arrows ---

  /** Returns all arrows (i.e. the hom-set) from `this` to `that`. */
  // def arrowsTo[H[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
  //   that: H[N,NL,E,EL])(implicit ev: G[NL,E,EL] <:< H[N,NL,E,EL])
  //     : Vector[Arrow[N,NL,E,EL,N,NL,E,EL,H]] = ???


  // --- Isomorphisms ---

  // TODO: Maybe I should memoise and make some statistics about
  // the frequency at which I ask for the same two graphs.
  /** Graph isomorphism test. */
  def iso(that: BaseDiGraph[N,NL,E,EL]): Boolean =
    if (this eq that) true
    else (this.isConnected,that.isConnected) match {
      case (true,true) => connectedIso(that)
      case (false,false) => DiGraph.isos[N,NL,E,EL,BaseDiGraph](
        this.components,that.components,
        ((g: BaseDiGraph[N,NL,E,EL], h: BaseDiGraph[N,NL,E,EL]) =>
          g connectedIso h))
      case _ => false
    }

  /** Connected graph isomorphism test.
    *
    * This method **assumes** both graphs are connected.  In
    * particular, if any of the two graphs is non-connected, an
    * IllegalArgumentException will be thrown when trying to create
    * the bijection (ie a pair of `Injection`s) that make these two
    * graphs isomorphic.
    */
  def connectedIso(that: BaseDiGraph[N,NL,E,EL]): Boolean =
    (this eq that) ||
    ((this.nodes.size == that.nodes.size) &&
     (this.edges.size == that.edges.size) &&
      findBijection(that).isDefined)

  /** Finds a bijection, if any, between `this` and `that` graph.
    *
    * This method **assumes** both graphs are connected.
    * In particular, if any of the two graphs is non-connected,
    * an IllegalArgumentException will be thrown when trying to create
    * the bijection (ie `Arrow`) that make these two graphs isomorphic.
    */
  def findBijection[N2,E2<:DiEdgeLike[N2],
    H[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    that: H[N2,NL,E2,EL])(implicit ev: This <:< H[N,NL,E,EL])
      : Option[Arrow[N,NL,E,EL,N2,NL,E2,EL,H]] = {

    /** Tries to construct a total `Arrow` from a partial one.
      *
      * @param queue nodes that should be visited next, in order.
      * @param nodeMap partial injection on nodes that we are extending.
      * @param edgeMap partial injection on edges that we are extending.
      * @param seenNodes nodes seen in the image of the injection.
      * @param seenEdges nodes seen in the image of the injection.
      */
    def extendBijection(queue: Seq[(N,N2)], fn: Map[N,N2], fe: Map[E,E2],
      ns: Set[N2], es: Set[E2]): Option[Arrow[N,NL,E,EL,N2,NL,E2,EL,H]] =
      // If there's nothing else to visit, we stop and return the injection we found
      // TODO: Is "nothing else to visit" the same as "have visited everything"?
      if (queue.isEmpty) Some(Arrow(this.asThis,that,fn,fe))
      else {
        val (u, v) = queue.head
        if ((this(u).inDegree != that(v).inDegree) ||
            (this(u).outDegree != that(v).outDegree)) None
        else {
          // TODO: I should probably carry not just the edges here
          // but also the neighbours
          val uin = this(u).incoming.toVector groupBy (this(_).label)
          val uout = this(u).outgoing.toVector groupBy (this(_).label)
          val vin = that(v).incoming.toVector groupBy (that(_).label)
          val vout = that(v).outgoing.toVector groupBy (that(_).label)

          // if the nodes have the same degree and the sets of labels
          // are equal then there's a posibility that u matches v
          if ((uin.keySet != vin.keySet) ||
              (uout.keySet != vout.keySet) ||
              (uin exists { case (label, edges) =>
                edges.size != vin(label).size }) ||
              (uout exists { case (label, edges) =>
                edges.size != vout(label).size })) None
          else {
            // sort incoming and outgoing edges by the number of
            // combinations that we have to try to reject
            val uinSorted = uin.toVector.sortBy(_._2.size)
            val uoutSorted = uout.toVector.sortBy(_._2.size)

            def matchingEdges(xs: Vector[(Option[EL],Vector[E])],
              m: Map[Option[EL],Vector[E2]])
                : Vector[Vector[(E,N,E2,N2)]] =
              for ((label,edges) <- xs; ue <- edges)
              yield (for {
                ve <- m(label);
                val un = this(u).opp(ue)
                val vn = that(v).opp(ve)
                if this(un) matches that(vn)
              } yield (ue,un,ve,vn))

            // collect edges around u and v that match
            val edges = matchingEdges(uinSorted,vin) ++
                        matchingEdges(uoutSorted,vout)

            if (edges exists (_.isEmpty)) None
            else {
              val indices = Array.fill[Int](edges.length)(0)

              def updateIndices = {
                def loop(i: Int): Boolean = {
                  // if (!indices.contains(i))
                  //   println(s"indices = ${indices.toSeq}, i = $i")
                  indices(i) += 1
                  if (indices(i) >= edges(i).length) {
                    if ((i+1) >= edges.length) true
                    else {
                      indices(i) = 0
                      loop(i+1)
                    }
                  } else false
                }
                loop(0)
              }

              var finished = false
              var result: Option[Arrow[N,NL,E,EL,N2,NL,E2,EL,H]] = None
              while (result.isEmpty && !finished) {
                val nbs = (indices, edges).zipped map ((i, xs) => xs(i))
                var mfn = fn
                var mfe = fe
                var mes = es
                var mns = ns
                var q = queue.tail
                var failed = false
                for ((ue, un, ve, vn) <- nbs if failed == false) {
                  if (mfn contains un) {
                    if (mfn(un) == vn) {
                      if (mfe contains ue) {
                        if (mfe(ue) == ve) {
                          // un and ue are in the preimage...
                          // just skip this, it's the edge we are
                          // coming from
                          // println(s"we are coming from ($ue, $ve)")
                        } else {
                          // println(s"fail 1: mfe($ue) != $ve")
                          failed = true
                        }
                      } else {
                        // un is in the preimage but not ue
                        // Check that ve is not in the image
                        if (mes contains ve) {
                          // println(s"fail 2: mes doesn't contain $ve")
                          failed = true
                        } else {
                          // println(s"adding ($ue, $ve)")
                          mfe += (ue -> ve)
                          mes += ve
                        }
                      }
                    } else {
                      // println(s"fail 3: mfn($un) != $vn")
                      failed = true
                    }
                  } else {
                    if (mfe contains ue) {
                      // println(s"fail 4: mfe doesn't contain $ue")
                      failed = true
                    } else {
                      // un and ue are not in the preimage
                      // Check that vn and ve are not in the image
                      if (mns.contains(vn) || mes.contains(ve)) {
                        // println(s"fail 5: $un and $ue are not in the preimage, but $vn or $ve are")
                        failed = true
                      } else {
                        // println(s"adding ($ue, $ve) and ($un, $vn)")
                        mfn += (un -> vn)
                        mfe += (ue -> ve)
                        mes += ve
                        mns += vn
                        q = q :+ (un -> vn)
                      }
                    }
                  }
                }
                if (failed == false)
                  result = extendBijection(q, mfn, mfe, mns, mes)
                if (updateIndices)
                  finished = true
              }
              result
            }
          }
        }
      }

    if (this.nodes.size == 1 && that.nodes.size == 1) {
      if (this(this.nodes.head).label == that(that.nodes.head).label)
        // FIXME: What if `{this,that}.nodes.head` has self-loops?
        Some(Arrow(this.asThis,that,
          Map(this.nodes.head -> that.nodes.head),Map.empty[E,E2]))
      else None
    } else {
      // map node labels to nodes
      val domNodesByLabel = this.nodes groupBy (this(_).label)
      val codNodesByLabel = that.nodes groupBy (that(_).label)

      // the distribution of labels must be the same
      if ((domNodesByLabel.keySet != codNodesByLabel.keySet) ||
          (domNodesByLabel exists { case (l, ns) =>
            ns.size != codNodesByLabel(l).size })) None
      else {
        // look for the least populated label in the codomain
        val (label, codNodes) = codNodesByLabel minBy (_._2.size)

        // get an anchor in the domain for that label
        val anchor = domNodesByLabel(label).head

        codNodes.collectFirst({ c: N2 =>
          extendBijection(Vector(anchor -> c), Map(anchor -> c),
            Map.empty, Set.empty, Set.empty) }.unlift)
      }
    }
  }


  // --- Intersections and Unions ---

  import DiGraph.{Unifier,EdgeUnifier}

  /** Intersections of subobjects of `this` and `that` graph.
    *
    * @return the set of graph intersections with their respective
    *         product injections.
    */
  def intersections[N2,E2<:DiEdgeLike[N2],N3,E3<:DiEdgeLike[N3],
    H[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    that: H[N2,NL,E2,EL])(implicit
      nodeUnifier: Unifier[N,N2,N3],
      // TODO: Probably I should make edgeUnifier a (H[N3,NL,E3,EL],Map[N,N3],Map[N2,N3]) => Unifier instead of EdgeUnifier
      edgeUnifier: EdgeUnifier[N,N2,N3,E,E2,E3],
      graphBuilder: () => H[N3,NL,E3,EL],
      ev: This <:< H[N,NL,E,EL])
      : Seq[(H[N3,NL,E3,EL],
             Arrow[N3,NL,E3,EL,N ,NL,E ,EL,H],
             Arrow[N3,NL,E3,EL,N2,NL,E2,EL,H])] = {

    val g1nodes: Seq[N] = this.nodes.toSeq
    val g2nodes: Seq[N2] = that.nodes.toSeq

    // set of nodes in `that` indexed by nodes in `this` that match
    val nodeMatches: Map[N,Seq[N2]] =
      (g1nodes, g1nodes map (u => g2nodes filter (v =>
        this(u) matches that(v)))).zipped.toMap
    // TODO: What if this(u) matches that(v) but not the other way?

    // all possible node intersections
    // TODO: Calling `cross` is unnecessarily slow and might blow up
    // the memory (unless it were to return a `Stream`).
    val nodeIntersections: Seq[Seq[Seq[(N,N2)]]] =
      for (i <- 0 to g1nodes.length;
           n1s <- g1nodes.combinations(i))
      yield cross(n1s map nodeMatches) map (n1s zip _)

    // construct intersections
    (for (ns <- nodeIntersections.flatten) yield {

      val g1nodes: Seq[N] = ns map (_._1)
      val g2nodes: Seq[N2] = ns map (_._2)

      // create base graph
      val nodes = for ((u,v) <- ns) yield nodeUnifier.unify(u,v)
      val g = graphBuilder()
      g.addNodes(nodes)

      // node mappings
      val fn1 = (nodes,g1nodes).zipped.toMap
      val fn2 = (nodes,g2nodes).zipped.toMap

      // add node labels
      for (n <- g.nodes)
        (this(fn1(n)).label, that(fn2(n)).label) match {
          case (Some(l1),Some(l2)) =>
            if (l1 == l2) g(n).label = l1
            else throw new IllegalArgumentException("labels '" + l1 +
              "' and '" + l2 + "' matched but are not equal")
          case (Some(l),None) => g(n).label = l
          case (None,Some(l)) => g(n).label = l
          case (None,None) => ()
        }

      // collect all edges between nodes in intersection
      val seen1 = mutable.Set[E]()
      val seen2 = mutable.Set[E2]()
      val edges: Seq[(E3,E,E2)] =
        for { u <- nodes;
              v <- nodes;
              e1 <- this(fn1(u)) edgesTo fn1(v);
              e2 <- that(fn2(u)) edgesTo fn2(v);
              // TODO: are e1 and e2 guaranteed to have the same
              // labels on the endpoint nodes?
              if !seen1(e1) && !seen2(e2) && (this(e1) matches that(e2));
              _ = seen1 += e1
              _ = seen2 += e2
        } yield (edgeUnifier.unify(e1,e2),e1,e2)

      // add subsets of found edges to intersection
      for (i <- 0 to edges.length;
           es <- edges.combinations(i)) yield {
        // put the new and old edges apart
        val (edges,g1edges,g2edges) = es.unzip3
        // graph with edges
        val h = graphBuilder() // g.copy
        h += g // little hack to make the type of `h` be G[...] instead of G[...]#G[...]
        h.addEdges(edges)
        // edge maps
        val fe1 = (edges,g1edges).zipped.toMap
        val fe2 = (edges,g2edges).zipped.toMap
        // add edge labels
        for ((e,e1,e2) <- es) (this(e1).label, that(e2).label) match {
          case (Some(l1),Some(l2)) =>
            if (l1 == l2) h(e).label = l1
            else throw new IllegalArgumentException("labels '" + l1 +
              "' and '" + l2 + "' matched but are not equal")
          case (Some(l),None) => h(e).label = l
          case (None,Some(l)) => h(e).label = l
          case (None,None) => ()
        }
        // create the matches
        // TODO: Why aren't these types inferred?
        (h,Arrow[N3,NL,E3,EL,N ,NL,E ,EL,H](h,this.asThis,fn1,fe1),
           Arrow[N3,NL,E3,EL,N2,NL,E2,EL,H](h,that,fn2,fe2))
      }
    }).flatten
  }

  /** Unions of subobjects of `this` and `that`. */
  def unions[N2,E2<:DiEdgeLike[N2],N3,E3<:DiEdgeLike[N3],
    H[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    that: H[N2,NL,E2,EL])(implicit
      nodeUnifier: Unifier[N,N2,N3],
      // TODO: Probably I should make edgeUnifier a (H[N3,NL,E3,EL],Map[N,N3],Map[N2,N3]) => Unifier instead of EdgeUnifier
      edgeUnifier: EdgeUnifier[N,N2,N3,E,E2,E3],
      graphBuilder: () => H[N3,NL,E3,EL],
      ev: This <:< H[N,NL,E,EL])
      : Seq[(H[N3,NL,E3,EL],
             Arrow[N ,NL,E ,EL,N3,NL,E3,EL,H],
             Arrow[N2,NL,E2,EL,N3,NL,E3,EL,H])] = {

    // This for shows that intersections and unions are in bijection
    for ((pb,f1,f2) <- intersections(that)(nodeUnifier,edgeUnifier,graphBuilder,ev)) yield {
      // create union
      val po: H[N3,NL,E3,EL] = graphBuilder() // pb.copy
      po += pb // little hack again, see intersections

      // missing nodes in intersection
      // transform the to `Seq`s to guarantee ordering for zipping
      val g1nodes = (this.nodes -- f1.n.values).toSeq
      val g2nodes = (that.nodes -- f2.n.values).toSeq
      // create missing nodes
      val n1s = for (u <- g1nodes) yield nodeUnifier.left(u)
      val n2s = for (v <- g2nodes) yield nodeUnifier.right(v)
      // add them to the graph
      po.addNodes(n1s ++ n2s)
      // create the node maps
      val fn1: Map[N,N3] = f1.n.inverse ++ (g1nodes, n1s).zipped.toMap
      val fn2: Map[N2,N3] = f2.n.inverse ++ (g2nodes, n2s).zipped.toMap
      // add node labels
      for (n <- g1nodes if this.nodelabels contains n)
        po(fn1(n)).label = this.nodelabels(n)
      for (n <- g2nodes if that.nodelabels contains n)
        po(fn2(n)).label = that.nodelabels(n)

      // missing edges in intersection
      val g1edges = (this.edges -- f1.e.values).toSeq
      val g2edges = (that.edges -- f2.e.values).toSeq
      // create missing outer edges
      edgeUnifier.initialise(pb,fn1,fn2)
      val e1s = for (e1 <- g1edges) yield edgeUnifier.left(e1)
      val e2s = for (e2 <- g2edges) yield edgeUnifier.right(e2)
      // add them to the graph
      po.addEdges(e1s ++ e2s)
      // create the edge maps
      val fe1: Map[E,E3] = f1.e.inverse ++ (g1edges,e1s).zipped.toMap
      val fe2: Map[E2,E3] = f2.e.inverse ++ (g2edges,e2s).zipped.toMap
      // add edge labels
      for (e <- g1edges if this.edgelabels contains e)
        po(fe1(e)).label = this.edgelabels(e)
      for (e <- g2edges if that.edgelabels contains e)
        po(fe2(e)).label = that.edgelabels(e)

      // TODO: Why aren't these types inferred?
      (po,Arrow[N ,NL,E ,EL,N3,NL,E3,EL,H](this.asThis,po,fn1,fe1),
          Arrow[N2,NL,E2,EL,N3,NL,E3,EL,H](that,po,fn2,fe2))
    }
  }
}

trait ConcreteDiGraph[N,NL,E<:DiEdgeLike[N],EL,
  H[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,H]]
    extends BaseDiGraph[N,NL,E,EL] {
  // type EdgeUpperBound[X] = DiEdgeLike[X]
  // type G[X,Y,Z<:DiEdgeLike[X],W] = H[X,Y,Z,W]
  type G[Y,Z<:E,W] = H[N,Y,Z,W]
}

class DiGraph[N,NL,E<:DiEdgeLike[N],EL]
    extends BaseDiGraph[N,NL,E,EL]
       with ConcreteDiGraph[N,NL,E,EL,DiGraph] {
  def empty = new DiGraph[N,NL,E,EL]
  def asThis = this
}

object DiGraph {

  // --- Constructors ---

  private def const[N,NL,E<:DiEdgeLike[N],EL](
    nodes: Traversable[(N,Option[NL])],
    edges: Traversable[(E,Option[EL])]): DiGraph[N,NL,E,EL] = {
    val g = new DiGraph[N,NL,E,EL]
    g.addNodes(nodes map (_._1))
    g.addEdges(edges map (_._1))
    for ((n, Some(l)) <- nodes) g(n).label = l
    for ((e, Some(l)) <- edges) g(e).label = l
    g
  }

  def empty[N,NL,E<:DiEdgeLike[N],EL] = new DiGraph[N,NL,E,EL] // = const(List(), List())

  def apply[N,NL](n1: (N,Option[NL]), nodes: (N,Option[NL])*) = new {
    def apply[E<:DiEdgeLike[N],EL](edges: (E,Option[EL])*) =
      const(n1 +: nodes, edges)
    def apply() = const[N,NL,IdDiEdge[Int,N],String](n1 +: nodes, List())
  }

  def withType[N,NL,E<:DiEdgeLike[N],EL] = new {
    def apply(nodes: (N,Option[NL])*)(edges: (E,Option[EL])*) =
      const(nodes, edges)
  }


  // -- Node and Edge Unifiers (for intersections and unions) --

  trait Unifier[T,U,V] {
    def unify(x: T, y: U): V
    def left(x: T): V
    def right(y: U): V
  }

  trait EdgeUnifier[N1,N2,N3,
    E1<:DiEdgeLike[N1],E2<:DiEdgeLike[N2],E3<:DiEdgeLike[N3]]
      extends Unifier[E1,E2,E3] {
    def initialise[NL,EL,G[X,Y,Z<:DiEdgeLike[X],W]<:BaseDiGraph[X,Y,Z,W]](
      g: G[N3,NL,E3,EL],
      leftNodeMap: Map[N1,N3],
      rightNodeMap: Map[N2,N3]): Unit
  }

  // -- Isomorphisms of multiple directed graphs --

  def isos[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    gs: Traversable[G[N,NL,E,EL]],
    hs: Traversable[G[N,NL,E,EL]],
    isoFn: (G[N,NL,E,EL],G[N,NL,E,EL]) => Boolean): Boolean =
    if (gs.size != hs.size) false
    else {
      // TODO: Better name than xsBySize?
      val gsBySize = gs groupBy (_.nodes.size)
      val hsBySize = hs groupBy (_.nodes.size)
      if (gsBySize.keySet != hsBySize.keySet) false
      else {
        var ok = true
        for ((n, gsn) <- gsBySize if ok) { // gsn are the graphs of (node set) size n
          val hsn = hsBySize(n)
          if (gsn.size != hsn.size) ok = false
          else {
            // TODO: Better name than xsnBySize?
            val gsnBySize = gsn groupBy (_.edges.size)
            val hsnBySize = hsn groupBy (_.edges.size)
            if (gsnBySize.keySet != hsnBySize.keySet) ok = false
            else for ((m,gsnm) <- gsnBySize if ok) {
              val hsnm = hsnBySize(m).to[mutable.ArrayBuffer]
              if (gsnm.size != hsnm.size) ok = false
              else for (g <- gsnm if ok) {
                hsnm find (isoFn(g,_)) match {
                  case Some(h) => hsnm -= h
                  case None => ok = false
                }
              }
            }
          }
        }
        ok
      }
    }

  def isos[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    gs: Traversable[G[N,NL,E,EL]],
    hs: Traversable[G[N,NL,E,EL]]): Boolean = isos(gs,hs,
      (g: G[N,NL,E,EL], h: G[N,NL,E,EL]) => g iso h)
}

