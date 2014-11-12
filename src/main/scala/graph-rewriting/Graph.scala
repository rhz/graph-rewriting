package graph_rewriting

import scala.annotation.tailrec
import scala.collection.mutable

// This is needed because mutable.Map.keySet returns a collection.Set
// and thus Node.edges has to be of this type.  Then the line
// adjacency(n)(e) = (e.nodes - n) forces adjacency to be of type
// mutable.Map[N, mutable.Map[E, collection.Set[N]]] and so it
// propagates everywhere.
import scala.collection.Set

import utils._
import implicits._

class Graph[N,NL,E<:EdgeLike[N],EL] {
  graph =>

  import Graph._

  def stringPrefix = "Graph"
  override def toString = s"$stringPrefix(" +
  s"nodes = $nodes, edges = $edges" +
  (if (nodelabels.nonEmpty) s", nodelabels = $nodelabels" else "") +
  (if (edgelabels.nonEmpty) s", edgelabels = $edgelabels" else "") + ")"

  def copy = {
    val g = new Graph[N,NL,E,EL]
    g.addNodes(nodes)
    g.addEdges(edges)
    for ((n, l) <- nodelabels) g(n).label = l
    for ((e, l) <- edgelabels) g(e).label = l
    g
  }

  def isEmpty: Boolean = nodes.isEmpty

  // --- Nodes and edges ---

  val nodes = mutable.Set.empty[N]
  val edges = mutable.Set.empty[E]
  val nodelabels = mutable.Map.empty[N, NL]
  val edgelabels = mutable.Map.empty[E, EL]
  val adjacency = mutable.Map.empty[N, mutable.Map[E, Set[N]]]

  // - Accessing inner nodes and edges -

  class Node(n: N) {
    @inline def value: N = n
    @inline def label: Option[NL] = nodelabels get n
    @inline def label_= (l: NL) = nodelabels(n) = l
    @inline def isLabelled: Boolean = nodelabels isDefinedAt n
    @inline def unlabel: Unit = nodelabels -= n
    type Other = Graph[_,_,_,_]
    def matches(that: Other#Node) =
      !this.isLabelled || (that.isLabelled && this.label == that.label)
    // TODO: should these be in a subclass specialised for DiEdges?
    // or should they just throw a UnsupportedOperation?
    def edges: Set[E] = adjacency(n).keySet
    def outgoing: Set[E] = edges collect { case e: DiEdgeLike[_]
      if e.source == n => e.asInstanceOf[E] }
    def incoming: Set[E] = edges collect { case e: DiEdgeLike[_]
      if e.target == n => e.asInstanceOf[E] }
    def edgesWith(m: N): Iterable[E] =
      adjacency(n) withFilter (_._2 contains m) map (_._1)
    def edgesTo(m: N): Set[E] = edges collect { case e: DiEdgeLike[_]
      if e.source == n && e.target == m => e.asInstanceOf[E] }
    def edgesFrom(m: N): Set[E] = ???
    def degree: Int = adjacency(n).size
    def inDegree: Int = incoming.size
    def outDegree: Int = outgoing.size
    def neighbours: Set[N] = adjacency(n).values.flatten.toSet
    // TODO: Should this be somewhere else?
    // It should not really be necessary
    def opp(e: E): N = e match {
      case e: DiEdgeLike[_] =>
        if      (e.source == n) e.target
        else if (e.target == n) e.source
        else throw new IllegalArgumentException("node " + n +
          " is not the source nor the target of edge " + e)
      case _ => throw new IllegalArgumentException(
        "edge " + e + " is not of type DiEdgeLike")
    }
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
    type Other = Graph[_,_,_,_]
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
  def += (g: Graph[N,NL,E,EL]): this.type = {
    addNodes(g.nodes)
    addEdges(g.edges)
    for ((n, l) <- g.nodelabels) nodelabels(n) = l
    for ((e, l) <- g.edgelabels) edgelabels(e) = l
    this
  }
  def + (n: N): Graph[N,NL,E,EL] = copy += n
  def + (e: E): Graph[N,NL,E,EL] = copy += e
  def + (g: Graph[N,NL,E,EL]): Graph[N,NL,E,EL] = copy += g

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
  def -= (g: Graph[N,NL,E,EL]): this.type = {
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
  def subgraphOf(that: Graph[N,NL,E,EL]): Boolean =
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
  def findRoot(n: N, parent: Map[N, N]): (N, Map[N, N]) =
    if (parent(n) == n) (n, parent)
    else {
      val (m, p) = findRoot(parent(n), parent)
      (m, p + (n -> m))
    }

  /** Disjoint set union. */
  def disjunion(n: N, m: N, parent: Map[N, N]): Map[N, N] = {
    val (x, p1) = findRoot(n, parent)
    val (y, p2) = findRoot(m, p1)
    if (x == y) p2
    else p2 + (x -> y)
  }

  /** Returns map from each node in this graph to its parent node in
    * the tree representing its disjoint set (ie connected component).
    */
  def parents: Map[N, N] =
    edges.foldLeft((nodes, nodes).zipped.toMap)({
      case (parent, e) => {
        val n = e.nodes.head
        e.nodes.tail.foldLeft(parent)({
          case (parent, m) => disjunion(n, m, parent) })
      }
    })

  /** Returns map from roots of each disjoint set to the set of nodes
    * in the set.
    */
  def disjointsByRoot: Map[N, Set[N]] = {
    val ps = parents
    ps.foldLeft((ps,
      Map.empty[N, Set[N]] withDefaultValue Set.empty[N]))({
        case ((parents, disjs), (n, p)) => {
          val (root, ps) = findRoot(p, parents)
          (ps, disjs + (root -> (disjs(root) + n)))
        }
      })._2
  }

  /** Collection of disjoint sets in this graph. */
  def disjoints: Iterable[Set[N]] = disjointsByRoot.values

  /** `true` if this graph is connected. */
  def isConnected: Boolean = disjointsByRoot.size == 1

  /** Returns the collection of connected components as separate graphs. */
  def components: Iterable[Graph[N,NL,E,EL]] =
    for (ns <- disjoints) yield inducedSubgraph(ns)

  /** Constructs an induced subgraph of this graph given the set of
    * nodes `ns`.
    */
  def inducedSubgraph(ns: Set[N]): Graph[N,NL,E,EL] = {
    val g = new Graph[N,NL,E,EL]
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

  def inducedSubgraph(n: N, ns: N*): Graph[N,NL,E,EL] =
    inducedSubgraph(Set(n) ++ ns)


  // --- Equality ---

  /** Graph equality. */
  def sameAs(that: Graph[N,NL,E,EL]): Boolean =
    (this subgraphOf that) && (that subgraphOf this)

  def canEqual(other: Any) = other.isInstanceOf[Graph[_,_,_,_]]

  override def equals(other: Any): Boolean = other match {
    case that: Graph[_,_,_,_] =>
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
}

object Graph {

  // --- Constructors ---

  def apply[N,NL,E<:EdgeLike[N],EL](
    nodes: Traversable[N],
    nodelabels: Traversable[(N, NL)],
    edges: Traversable[E],
    edgelabels: Traversable[(E, EL)]): Graph[N,NL,E,EL] = {
    val g = new Graph[N,NL,E,EL]
    g.addNodes(nodes)
    g.addEdges(edges)
    for ((n, l) <- nodelabels) g(n).label = l
    for ((e, l) <- edgelabels) g(e).label = l
    g
  }

  // FIXME: ambiguous reference to overloaded definition (why?)
  // def apply[N,NL,E,EL](nodes: (N,NL)*)(edges: (E,EL)*)(
  //   implicit d: DummyImplicit): Graph[N,NL,E,EL] =
  //   Graph(nodes map (_._1), nodes, edges map (_._1), edges)

  // IdDiEdge is the default for E
  def apply[N,NL,EL](nodes: (N,NL)*)(edges: (IdDiEdge[Int,N],EL)*)
      : Graph[N,NL,IdDiEdge[Int,N],EL] =
    Graph(nodes map (_._1), nodes, edges map (_._1), edges)

  // String is the default for EL
  def apply[N,NL](nodes: (N,NL)*)(e1: IdDiEdge[Int,N],
    edges: IdDiEdge[Int,N]*): Graph[N,NL,IdDiEdge[Int,N],String] =
    Graph(nodes map (_._1), nodes, e1 +: edges, List())

  // String is the default for NL
  def apply[N,EL](n1: N, nodes: N*)(edges: (IdDiEdge[Int,N],EL)*)
      : Graph[N,String,IdDiEdge[Int,N],EL] =
    Graph(n1 +: nodes, List(), edges map (_._1), edges)

  // String is the default for NL and EL
  def apply[N](n1: N, nodes: N*)(e1: IdDiEdge[Int,N],
    edges: IdDiEdge[Int,N]*): Graph[N,String,IdDiEdge[Int,N],String] =
    Graph[N,String,IdDiEdge[Int,N],String](
      n1 +: nodes, List(), e1 +: edges, List())

  // --- Isomorphisms ---

  /** Graph isomorphism test. */
  def iso[N,NL,E<:DiEdgeLike[N],EL](
    g1: Graph[N,NL,E,EL], g2: Graph[N,NL,E,EL]): Boolean =
    if (g1 eq g2) true
    else (g1.isConnected, g2.isConnected) match {
      case (true, true) => connectedIso(g1, g2)
      case (false, false) => isos(g1.components, g2.components,
        (g: Graph[N,NL,E,EL], h: Graph[N,NL,E,EL]) =>
          connectedIso(g, h))
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
  // TODO: Check with: Graph(u1->u2,u1->u3,u1->u3) connectedIso
  // Graph(v1->v1,v1->v2,v1->v3) and injection
  // Arrow(u1->v1,u2->v2,u2->v3,u3->v1)
  def connectedIso[N,NL,E<:DiEdgeLike[N],EL](
    g1: Graph[N,NL,E,EL], g2: Graph[N,NL,E,EL]): Boolean =
    (g1 eq g2) ||
    ((g1.nodes.size == g2.nodes.size) &&
     (g1.edges.size == g2.edges.size) &&
     findBijection(g1, g2).isDefined)

  def isos[N,NL,E<:DiEdgeLike[N],EL](
    gs1: Traversable[Graph[N,NL,E,EL]],
    gs2: Traversable[Graph[N,NL,E,EL]],
    isoFn: (Graph[N,NL,E,EL],Graph[N,NL,E,EL]) => Boolean): Boolean =
    if (gs1.size != gs2.size) false
    else {
      val gs1BySize = gs1 groupBy (_.nodes.size)
      val gs2BySize = gs2 groupBy (_.nodes.size)
      if (gs1BySize.keySet != gs2BySize.keySet) false
      else {
        var ok = true
        for ((nodesetSize, gs3) <- gs1BySize if ok) {
          val gs4 = gs2BySize(nodesetSize)
          if (gs3.size != gs4.size) ok = false
          else {
            val gs3BySize = gs3 groupBy (_.edges.size)
            val gs4BySize = gs4 groupBy (_.edges.size)
            if (gs3BySize.keySet != gs4BySize.keySet) ok = false
            else for ((edgesetSize, gs5) <- gs3BySize if ok) {
              val gs6 = gs4BySize(edgesetSize).to[mutable.ArrayBuffer]
              if (gs5.size != gs6.size) ok = false
              else for (g5 <- gs5 if ok) {
                gs6 find (isoFn(g5, _)) match {
                  case Some(g6) => gs6 -= g6
                  case None => ok = false
                }
              }
            }
          }
        }
        ok
      }
    }

  def isos[N,NL,E<:DiEdgeLike[N],EL](
    gs1: Traversable[Graph[N,NL,E,EL]],
    gs2: Traversable[Graph[N,NL,E,EL]])
      : Boolean = isos(gs1, gs2,
        (g: Graph[N,NL,E,EL], h: Graph[N,NL,E,EL]) => iso(g, h))

  /** Finds a bijection, if any, between `g1` graph and `g2` graph.
    *
    * This method **assumes** both graphs are connected.  In
    * particular, if any of the two graphs is non-connected, an
    * IllegalArgumentException will be thrown when trying to create
    * the bijection (ie a pair of `Injection`s) that make these two
    * graphs isomorphic.
    */
  // TODO: Make a function for undirected graphs.
  def findBijection[N,NL,E<:DiEdgeLike[N],EL](
    g1: Graph[N,NL,E,EL],
    g2: Graph[N,NL,E,EL])
      : Option[Arrow[N,NL,E,EL,N,NL,E,EL]] = {

    /** Tries to construct a total `Arrow` from a partial one.
      *
      * @param queue nodes that should be visited next, in order.
      * @param nodeMap partial injection on nodes that we are extending.
      * @param edgeMap partial injection on edges that we are extending.
      * @param seenNodes nodes seen in the image of the injection.
      * @param seenEdges nodes seen in the image of the injection.
      */
    def extendBijection(queue: Seq[(N,N)], fn: Map[N,N], fe: Map[E,E],
      ns: Set[N], es: Set[E])
        : Option[Arrow[N,NL,E,EL,N,NL,E,EL]] =
      // If there's nothing else to visit, we stop and return the injection we found
      // TODO: Is "nothing else to visit" the same as "have visited everything"?
      if (queue.isEmpty) Some(Arrow(g1, g2, fn, fe))
      else {
        val (u, v) = queue.head
        // println("u = " + u + ", v = " + v)
        if ((g1(u).inDegree  != g2(v).inDegree) ||
            (g1(u).outDegree != g2(v).outDegree)) None
        else {
          // TODO: I should probably carry not just the edges here
          // but also the neighbours
          val uin  = g1(u).incoming.toVector groupBy (g1(_).label)
          val vin  = g2(v).incoming.toVector groupBy (g2(_).label)
          val uout = g1(u).outgoing.toVector groupBy (g1(_).label)
          val vout = g2(v).outgoing.toVector groupBy (g2(_).label)
          // println("uin = " + uin)
          // println("uout = " + uout)
          // println("vin = " + vin)
          // println("vout = " + vout)

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
            val  uinSorted =  uin.toVector.sortBy(_._2.size)
            val uoutSorted = uout.toVector.sortBy(_._2.size)

            def matchingEdges(xs: Vector[(Option[EL], Vector[E])],
              m: Map[Option[EL], Vector[E]])
                : Vector[Vector[(E,N,E,N)]] =
              for ((label, edges) <- xs; ue <- edges)
              yield (for {
                ve <- m(label);
                val un = g1(u).opp(ue)
                val vn = g2(v).opp(ve)
                if g1(un) matches g2(vn)
              } yield (ue, un, ve, vn))

            // collect edges around u and v that match
            val edges = matchingEdges(uinSorted, vin) ++
              matchingEdges(uoutSorted, vout)
            // println("edges = " + edges)

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
              var result: Option[Arrow[N,NL,E,EL,N,NL,E,EL]] = None
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

    if (g1.nodes.size == 1 && g2.nodes.size == 1) {
      if (g1(g1.nodes.head).label == g2(g2.nodes.head).label)
        Some(Arrow(g1, g2, Map(g1.nodes.head -> g2.nodes.head),
          Map.empty[E,E]))
      else None
    } else {
      // map node labels to nodes
      val domNodesByLabel = g1.nodes groupBy (g1(_).label)
      val codNodesByLabel = g2.nodes groupBy (g2(_).label)

      // the distribution of labels must be the same
      if ((domNodesByLabel.keySet != codNodesByLabel.keySet) ||
          (domNodesByLabel exists { case (l, ns) =>
            ns.size != codNodesByLabel(l).size })) None
      else {
        // look for the least populated label in the codomain
        val (label, codNodes) = codNodesByLabel minBy (_._2.size)

        // get an anchor in the domain for that label
        val anchor = domNodesByLabel(label).head

        codNodes.collectFirst({ c: N =>
          extendBijection(Vector(anchor -> c), Map(anchor -> c),
            Map.empty, Set.empty, Set.empty) }.unlift)
      }
    }
  }

  // --- Intersections and Unions ---

  /** Intersections of subobjects of `g1` and `g2`.
    *
    * @return the set of graph intersections with their respective
    *         product injections.
    */
  def intersections[N1,NL,E1<:DiEdgeLike[N1],EL,
                    N2,   E2<:DiEdgeLike[N2]](
    g1: Graph[N1,NL,E1,EL],
    g2: Graph[N2,NL,E2,EL])
      : Seq[(Graph[String,NL,IdDiEdge[Int,String],EL],
             Arrow[String,NL,IdDiEdge[Int,String],EL,N1,NL,E1,EL],
             Arrow[String,NL,IdDiEdge[Int,String],EL,N2,NL,E2,EL])] = {

    type N = String
    type E = IdDiEdge[Int, N]

    val g1nodes: Seq[N1] = g1.nodes.toSeq
    val g2nodes: Seq[N2] = g2.nodes.toSeq

    // set of nodes in `g2` indexed by nodes in `g1` that match
    val nodeMatches: Map[N1, Seq[N2]] =
      (g1nodes, g1nodes map (u => g2nodes filter (v =>
        g1(u) matches g2(v)))).zipped.toMap
    // TODO: What if g1(u) matches g2(v) but not the opposite?

    // TODO: Calling `cross` is unnecessarily slow and might blow up
    // the memory.
    // all possible node intersections
    val nodeIntersections: Seq[Seq[Seq[(N1, N2)]]] =
      for (i <- 0 to g1nodes.length;
           n1s <- g1nodes.combinations(i))
      yield cross(n1s map nodeMatches) map (n1s zip _)

    // construct intersections
    (for (ns <- nodeIntersections.flatten) yield {

      val g1nodes: Seq[N1] = ns map (_._1)
      val g2nodes: Seq[N2] = ns map (_._2)

      // create base graph
      val nodes = for ((u, v) <- ns) yield "(" + u + "," + v + ")"
      val g = new Graph[N,NL,E,EL]
      g.addNodes(nodes)

      // node mappings
      val fn1 = (nodes, g1nodes).zipped.toMap
      val fn2 = (nodes, g2nodes).zipped.toMap

      // add node labels
      for (n <- g.nodes)
        (g1(fn1(n)).label, g2(fn2(n)).label) match {
          case (Some(l1), Some(l2)) =>
            if (l1 == l2) g(n).label = l1
            else throw new IllegalArgumentException("labels '" + l1 +
              "' and '" + l2 + "' matched but are not equal")
          case (Some(l), None) => g(n).label = l
          case (None, Some(l)) => g(n).label = l
          case (None, None) => ()
        }

      // collect all edges between nodes in intersection
      val seen1 = mutable.Set[E1]()
      val seen2 = mutable.Set[E2]()
      val cnt = Counter()
      val edges: Seq[(E, E1, E2)] =
        for { u <- nodes;
              v <- nodes;
              e1 <- g1(fn1(u)) edgesTo fn1(v);
              e2 <- g2(fn2(u)) edgesTo fn2(v);
              // TODO: are e1 and e2 guaranteed to have the same
              // labels on the endpoint nodes?
              if !seen1(e1) && !seen2(e2) && (g1(e1) matches g2(e2));
              _ = seen1 += e1
              _ = seen2 += e2
        } yield (IdDiEdge(cnt.next, u, v), e1, e2)

      // add subsets of found edges to intersection
      for (i <- 0 to edges.length;
           es <- edges.combinations(i)) yield {
        // put the new and old edges apart
        val (edges, g1edges, g2edges) = es.unzip3
        // graph with edges
        val h = g.copy
        h.addEdges(edges)
        // edge maps
        val fe1 = (edges, g1edges).zipped.toMap
        val fe2 = (edges, g2edges).zipped.toMap
        // add edge labels
        for ((e, e1, e2) <- es) (g1(e1).label, g2(e2).label) match {
          case (Some(l1), Some(l2)) =>
            if (l1 == l2) h(e).label = l1
            else throw new IllegalArgumentException("labels '" + l1 +
              "' and '" + l2 + "' matched but are not equal")
          case (Some(l), None) => h(e).label = l
          case (None, Some(l)) => h(e).label = l
          case (None, None) => ()
        }
        // create the matches
        (h, Arrow(h, g1, fn1, fe1), Arrow(h, g2, fn2, fe2))
      }
    }).flatten
  }

  /** Unions of subobjects of `g1` and `g2`. */
  def unions[N1,NL,E1<:DiEdgeLike[N1],EL,
             N2,   E2<:DiEdgeLike[N2]](
    g1: Graph[N1,NL,E1,EL],
    g2: Graph[N2,NL,E2,EL])
      : Seq[(Graph[String,NL,IdDiEdge[Int,String],EL],
             Arrow[N1,NL,E1,EL,String,NL,IdDiEdge[Int,String],EL],
             Arrow[N2,NL,E2,EL,String,NL,IdDiEdge[Int,String],EL])] = {

    type N = String
    type E = IdDiEdge[Int, N]

    // This for shows that intersections and unions are in bijection
    for ((pb, f1, f2) <- intersections(g1, g2)) yield {
      // create union
      val po: Graph[N,NL,E,EL] = pb.copy

      // missing nodes in intersection
      // transform the to `Seq`s to guarantee ordering for zipping
      val g1nodes = (g1.nodes -- f1.n.values).toSeq
      val g2nodes = (g2.nodes -- f2.n.values).toSeq
      // create missing nodes
      val n1s = for (u <- g1nodes) yield "("  + u + ",)"
      val n2s = for (v <- g2nodes) yield "(," + v +  ")"
      // add them to the graph
      po.addNodes(n1s ++ n2s)
      // create the node maps
      val fn1: Map[N1, N] = f1.n.inverse ++ (g1nodes, n1s).zipped.toMap
      val fn2: Map[N2, N] = f2.n.inverse ++ (g2nodes, n2s).zipped.toMap
      // add node labels
      for (n <- g1nodes if g1.nodelabels contains n)
        po(fn1(n)).label = g1.nodelabels(n)
      for (n <- g2nodes if g2.nodelabels contains n)
        po(fn2(n)).label = g2.nodelabels(n)

      // missing edges in intersection
      val g1edges = (g1.edges -- f1.e.values).toSeq
      val g2edges = (g2.edges -- f2.e.values).toSeq
      // create missing outer edges
      val maxEdgeId = ((for (IdDiEdge(id, _, _) <- pb.edges)
                        yield id) + 0).max
      val cnt = Counter(maxEdgeId + 1)
      val e1s = for (e1 <- g1edges) yield
        IdDiEdge(cnt.next, fn1(e1.source), fn1(e1.target))
      val e2s = for (e2 <- g2edges) yield
        IdDiEdge(cnt.next, fn2(e2.source), fn2(e2.target))
      // add them to the graph
      po.addEdges(e1s ++ e2s)
      // create the edge maps
      val fe1: Map[E1, E] = f1.e.inverse ++ (g1edges, e1s).zipped.toMap
      val fe2: Map[E2, E] = f2.e.inverse ++ (g2edges, e2s).zipped.toMap
      // add edge labels
      for (e <- g1edges if g1.edgelabels contains e)
        po(fe1(e)).label = g1.edgelabels(e)
      for (e <- g2edges if g2.edgelabels contains e)
        po(fe2(e)).label = g2.edgelabels(e)

      (po, Arrow(g1, po, fn1, fe1), Arrow(g2, po, fn2, fe2))
    }
  }
}

