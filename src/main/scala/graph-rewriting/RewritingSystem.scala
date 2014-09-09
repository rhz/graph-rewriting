package graph_rewriting

import scala.language.postfixOps
import scala.annotation.tailrec

import scala.reflect.runtime.universe.{TypeTag, typeTag}
import scala.reflect.{ClassTag, classTag}

import scala.collection.mutable
import mutable.ArrayBuffer

import scalax.{collection => c}
import c.GraphEdge._ // EdgeCopy,...
import c.GraphPredef._ // OuterEdge,Param

// List of FIXMEs:
// 1. Check that node created by AddNode is not in the codomain of
//    the match.

object RewritingSystem {

  // --- Helper functions ---

  /** Pick an element of each sequence non-deterministically. */
  def cross[A](xss: Seq[Seq[A]], seen: Set[A] = Set[A]())
      : Seq[Seq[A]] = xss match {
    case Seq() => List(List())
    case xs +: xss =>
      for { y <- xs if !seen(y);
            yss <- cross(xss, seen + y)
      } yield (y +: yss)
  }

  /** Concatenate `Seq`s in pairs in the obvious way. */
  def concatPairs[A, B](xys: Iterable[(Set[A], Set[B])])
      : (Set[A], Set[B]) =
    xys.foldRight((Set[A](), Set[B]())) {
      case ((xs, ys), (xss, yss)) => (xs ++: xss, ys ++: yss) }

  /** Returns the node sitting at the other end of the edge `e` in graph `g`. */
  def opp(g: Graph)(e: g.EdgeT, n: g.NodeT): g.NodeT =
    if (e.source == n) e.target
    else e.source

  /** Find an inner edge equivalent to the given outer edge. */
  // TODO: This needs testing. What does findEntry actually do?
  // Does findEntry requires the edge's hashCode method to use
  // some combination of the nodes and label hashCode?
  def findEdge(g: Graph, e: EqDiEdge[Node]): Option[g.EdgeT] =
    g find e.source flatMap { innerNode =>
      Option(innerNode.edges.findEntry(e,
        (i: g.EdgeT, o: EqDiEdge[Node]) => true)) }

  /** Pair inner edges in two graphs using `=~=`. */
  def pair(g1: Graph, g2: Graph)(
    edges1: Seq[g1.EdgeT],
    edges2: Set[g2.EdgeT])
      : Seq[(g1.EdgeT, g2.EdgeT)] =
    edges1 match {
      case Seq() => List()
      // FIXME: I shouldn't need `toOuter` at all in the next line,
      // but when I remove them, I get a MatchException in line 420
      case e1 +: rest1 => edges2 find (_.toOuter =~= e1.toOuter) match {
        case Some(e2) => (e1, e2) +: pair(g1, g2)(rest1, edges2 - e2)
        case None => throw new IllegalArgumentException(
          "edge " + e1 + " doesn't pair with any edge in " + edges2)
      }
    }

  def isos(gs1: Iterable[Graph], gs2: Iterable[Graph],
    isoFn: (Graph, Graph) => Boolean): Boolean =
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


  /** Implicit class transforming `Function1`s that return `Option`
    * into `PartialFunction`s.
    */
  implicit class UnliftableFunction[A,B](f: A => Option[B]) {

    def unlift = new PartialFunction[A,B] {
      private[this] var tested = false
      private[this] var arg: A = _
      private[this] var ans: Option[B] = None
      private[this] def cache(a: A) {
        if (!tested) {
          tested = true
          arg = a
          ans = f(a)
        } else if (a != arg) {
          arg = a
          ans = f(a)
        }
      }
      def isDefinedAt(a: A) = {
        cache(a)
        ans.isDefined
      }
      def apply(a: A) = {
        cache(a)
        ans.get
      }
    }
  }


  // --- Graphs ---

  type Graph = c.mutable.Graph[Node, EqDiEdge]

  // import Graph companion object
  val Graph = c.mutable.Graph

  // Enrich labelled graphs
  /** Wrapper around `scalax.collection.mutable.Graph` to add methods
    * to this class, e.g. an isomorphism test or splitting into
    * connected components.
    */
  implicit final class GraphWrapper(val g: Graph) {

    /** Test whether this graph is a subgraph of `that`. */
    def subgraphOf(that: Graph): Boolean = g.nodes.forall(n1 =>
      that.nodes exists (n2 => /*n1 =~= n2 &&*/ n1 == n2)) &&
      g.edges.forall(e1 => that.edges exists (e1.toOuter =~= _.toOuter))

    /** Graph equality. */
    def sameAs(that: Graph): Boolean =
      (this subgraphOf that) && (that subgraphOf g)

    lazy val isConnected = g.isConnected

    /** Graph isomorphism test. */
    def isIsoTo[L: ClassTag](that: Graph): Boolean =
      if (g eq that) true
      else {
        val thatIsConnected = that.isConnected
        if (this.isConnected && thatIsConnected) connectedIsoTo(that)
        else if (!this.isConnected && !thatIsConnected) {
          val thisCcs = this.split
          val thatCcs = that.split
          isos(thisCcs, thatCcs, ((g, h) => g.connectedIsoTo[L](h)))
        } else false
      }

    /** Connected graph isomorphism test.
      *
      * This method **assumes** both graphs are connected.  In
      * particular, if any of the two graphs is non-connected, an
      * IllegalArgumentException will be thrown when trying to create
      * the bijection (ie a pair of `Injection`s) that make these two
      * graphs isomorphic.
      */
    // TODO: Check with: u1->u2,u1->u3,u1->u3 connectedIsoTo[String] v1->v1,v1->v2,v1->v3
    // and injection: u1 -> v1, u2 -> v2, u2 -> v3, u3 -> v1
    def connectedIsoTo[L: ClassTag](that: Graph): Boolean =
      (g eq that) ||
      ((g.nodes.length == that.nodes.length) &&
       (g.edges.length == that.edges.length) &&
       findBijection[L](that).isDefined)

    /** Finds a bijection, if any, between `this` graph and `that` graph.
      *
      * This method **assumes** both graphs are connected.  In
      * particular, if any of the two graphs is non-connected, an
      * IllegalArgumentException will be thrown when trying to create
      * the bijection (ie a pair of `Injection`s) that make these two
      * graphs isomorphic.
      */
    def findBijection[L: ClassTag](that: Graph): Option[(Injection, Injection)] = {
      // TODO: Move `mkInj` one level up (to GraphWrapper)?
      // TODO: Make this (non-deterministic?) function tail-recursive?
      // @tailrec
      /** Tries to construct an `Injection` from a partial injection.
        *
        * @param queue nodes that should be visited next, in order.
        * @param nodeMap partial injection on nodes that we are extending.
        * @param edgeMap partial injection on edges that we are extending.
        * @param seenNodes nodes seen in the image of the injection.
        * @param seenEdges nodes seen in the image of the injection.
        */
      def mkInj(
        queue: mutable.Queue[(g.NodeT, that.NodeT)],
        nodeMap: mutable.Map[g.NodeT, that.NodeT],
        edgeMap: mutable.Map[g.EdgeT, that.EdgeT] = mutable.Map(),
        seenNodes: mutable.Set[that.NodeT] = mutable.Set(),
        seenEdges: mutable.Set[that.EdgeT] = mutable.Set())
          : Option[(Injection, Injection)] =
        // If there's nothing else to visit, we stop and return the Injection we found
        // TODO: Is "nothing else to visit" the same as "have visited everything"?
        if (queue.isEmpty) Some((
          Injection(g, that)(nodeMap.toMap, edgeMap.toMap),
          Injection(that, g)(nodeMap.map(_.swap).toMap,
                             edgeMap.map(_.swap).toMap)))
        else {
          val (u, v) = queue.dequeue

          if (u.edges.isEmpty && v.edges.isEmpty)
            Some(Injection(g, that)(Map(u -> v), Map()),
                 Injection(that, g)(Map(v -> u), Map()))
          else if ((u.inDegree != v.inDegree) ||
             (u.outDegree != v.outDegree)) None
          else {
            // Map labels to edges by filtering and grouping
            // It would be great if groupBy accepted a PartialFunction
            // TODO: Is this the most efficient way to do it?
            def edgesByLabel(g: Graph)(xs: Iterable[g.EdgeT]) =
              xs.foldLeft(Map.empty[L,Vector[g.EdgeT]])({
                case (m, e) => e.label match {
                  case l: L => if (m contains l) m + (l -> (m(l) :+ e))
                               else m + (l -> Vector(e))
                  case _ => throw new IllegalArgumentException(
                    "edge label not of type " +
                    classTag[L].runtimeClass.getName)
                }
              })

            val uin  = edgesByLabel(g   )(u.incoming)
            val vin  = edgesByLabel(that)(v.incoming)
            val uout = edgesByLabel(g   )(u.outgoing)
            val vout = edgesByLabel(that)(v.outgoing)

            // If the nodes have the same degree and the sets of labels are equal
            // then there's a posibility that u matches v
            if ((uin.keySet != vin.keySet) ||
                (uout.keySet != vout.keySet) ||
                (uin exists { case (label, edges) =>
                  edges.size != vin(label).size }) ||
                (uout exists { case (label, edges) =>
                  edges.size != vout(label).size })) None
            else {
              // Sort incoming and outgoing edges by the number of
              // combinations that we have to try to reject
              val  uinSorted =  uin.toVector.sortBy(_._2.size)
              val uoutSorted = uout.toVector.sortBy(_._2.size)

              def matchingEdges(xs: Vector[(L, Vector[g.EdgeT])],
                                m: Map[L, Vector[that.EdgeT]])
                  : Vector[Vector[(g.EdgeT,g.NodeT,that.EdgeT,that.NodeT)]] =
                for ((label, edges) <- xs; ue <- edges)
                yield (for {
                  ve <- m(label);
                  val un = opp(g   )(ue, u)
                  val vn = opp(that)(ve, v)
                  if un =~= vn
                  // also we know that u =~= v and
                  // ue.label == ve.label, thus ue =~= ve
                } yield (ue, un, ve, vn))

              // Collect edges around u and v that match
              val edges = matchingEdges(uinSorted, vin) ++
                matchingEdges(uoutSorted, vout)

              if (edges exists (_.isEmpty)) None
              else {
                val indices = Array.fill[Int](edges.length)(0)

                def updateIndices = {
                  def loop(i: Int): Boolean = {
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
                var result: Option[(Injection, Injection)] = None
                while (result.isEmpty && !finished) {
                  val nbs = (indices, edges).zipped map ((i, xs) => xs(i))

                  // TODO: Maybe using immutable data structures would
                  // make this faster, no cloning needed.
                  val nm = nodeMap.clone
                  val em = edgeMap.clone
                  lazy val seenN = seenNodes.clone
                  lazy val seenE = seenEdges.clone
                  lazy val q = queue.clone
                  var failed = false
                  for ((ue, un, ve, vn) <- nbs if failed == false) {
                    if (nm contains un) {
                      if (nm(un) == vn) {
                        if (em contains ue) {
                          if (em(ue) == ve) {
                            // un and ue are in the preimage...
                            // just skip this, it's the edge we are
                            // coming from
                          } else failed = true
                        } else {
                          // un is in the preimage but not ue
                          // Check that ve is not in the image
                          if (seenE contains ve) failed = true
                          else {
                            em += (ue -> ve)
                            seenE += ve
                          }
                        }
                      } else failed = true
                    } else {
                      if (em contains ue) failed = true
                      else {
                        // un and ue are not in the preimage
                        // Check that vn and ve are not in the image
                        if (seenN.contains(vn) || seenE.contains(ve))
                          failed = true
                        else {
                          nm += (un -> vn)
                          em += (ue -> ve)
                          seenE += ve
                          seenN += vn
                          q += (un -> vn)
                        }
                      }
                    }
                  }
                  if (failed == false)
                    result = mkInj(q, nm, em, seenN, seenE)
                  if (updateIndices)
                    finished = true
                }
                result
              }
            }
          }
        }

      // Map node labels to nodes
      val domNodesByLabel =    g.nodes groupBy (_.label)
      val codNodesByLabel = that.nodes groupBy (_.label)

      // The distribution of labels must be the same
      if ((domNodesByLabel.keySet == codNodesByLabel.keySet) &&
          (domNodesByLabel forall { case (l, ns) =>
            ns.size == codNodesByLabel(l).size })) {

        // Look for the least populated label in the codomain
        val (label, codNodes) = codNodesByLabel minBy (_._2.size)

        // Get an anchor in the domain for that label
        val anchor = domNodesByLabel(label).head

        codNodes collectFirst ({ c: that.NodeT =>
          mkInj(mutable.Queue(anchor -> c),
                  mutable.Map(anchor -> c))
        }).unlift
      } else None
    }

    def split: Iterable[Graph] =
      if (this.isConnected) List(g)
      else {
        val seen = mutable.Set.empty[g.NodeT]
        val cc = mutable.Map.empty[Int, Seq[g.NodeT]] withDefaultValue List()
        var i = 0
        @tailrec def assignToCc(queue: Set[g.NodeT]) {
          if (queue.nonEmpty) {
            val n: g.NodeT = queue.head
            cc(i) :+= n
            seen += n
            assignToCc(queue.tail ++ (n.neighbors -- seen))
          }
        }
        for (n <- g.nodes if !(seen contains n)) {
          assignToCc(Set(n))
          i += 1
        }
        for (nodes <- cc.values) yield {
          val edges = nodes.map(n =>
            n.edges.map(e => e.toOuter)).flatten.toSet
          Graph.from(nodes map (_.value), edges)
        }
      }
  }


  // --- Labelled Nodes ---
  // REMARK: The Node class seems a bit too concrete in comparison
  // with the EqDiEdge class, maybe name and label should be of type
  // N and L, respectively.

  // TODO: Replace Node by MatchableNode

  type Label = String

  /** Node class.
    *
    * @param name name of the node.
    * @param label label of the node.
    */
  class Node(val name: String, var label: Label) {

    def =~= (that: Node): Boolean =
      this.label.isEmpty || (this.label == that.label)

    override def equals(that: Any) = that match {
      case Node(nme,_) => this.name == nme
      case _ => false
    }

    def canEqual(that: Any) = that.isInstanceOf[Node]

    override def hashCode = name.hashCode

    override def toString = "\"" + name +
      (if (label.isEmpty) "" else ":" + label) + "\""
  }

  object Node {

    val regex = "([^,:]*)(:[^,:]+)?".r

    def apply(name: String, label: Label) = new Node(name, label)

    def apply(s: String): Node = s match {
      case regex(name, null)  => Node(name, "")
      case regex(name, label) => Node(name, label.tail)
      case _ => throw new IllegalArgumentException("illegal string " +
          s"""for a node: "$s" doesn't conform to regex $regex""")
    }

    def unapply(n: Node): Option[(String, Label)] =
      Some((n.name, n.label))
  }

  implicit def node(s: String): Node = Node(s)


  // --- Labelled (Multi-)Edges ---

  // TODO: Replace EqDiEdge by MatchableEdge

  /** Labelled directed multi-edge.
    *
    * @tparam N the type of nodes.
    * @param label label of the edge.
    */
  abstract class EqDiEdge[N](source: N, target: N)
      extends c.edge.LDiEdge[N](source, target)
         with EdgeCopy[EqDiEdge]
         with OuterEdge[N,EqDiEdge] {

    var label: L1

    override def copy[NN](newNodes: Iterable[NN]) = {
      require(newNodes.size == 2,
        "cannot create a copy of this edge with more than two endpoints")
      val ns = newNodes.iterator
      EqDiEdge(ns.next, ns.next)(label)
    }
    
    override def equals(other: Any) = other match {
      case that: EqDiEdge[_] => this eq that
      case _ => false
    }

    override def hashCode: Int = {
      // val h = System.identityHashCode(this)
      // (h << 1) - (h << 8) // for optimized hash distribution
      nodes.hashCode ^ label.hashCode
    }

    def =~= (that: EqDiEdge[_]): Boolean =
      // (this.label.isEmpty || (this.label == that.label))
      (this.label == that.label) && // baseEquals(that)
      // RHZ: Why does this compile? `source` is of type N and not
      // all N have a method `value` no?
      ((source.value, that.source.value) match {
        case (s1: Node, s2: Node) => s1 =~= s2 }) &&
      ((target.value, that.target.value) match {
        case (t1: Node, t2: Node) => t1 =~= t2 })

    override protected def nodesToStringSeparator =
      EqDiEdge.nodeSeparator

    override protected def attributesToString =
      "(\"" + label + "\")"

    override protected def nodesToStringWithParenthesis = true
    // override protected def nodesToString =
    //   stringPrefix + "(\"" + source + "\",\"" + target + "\")"
    override def stringPrefix = "EqDiEdge"

    override def toString = "(" + _1 + EqDiEdge.nodeSeparator + _2 +
      ")(\"" + label + "\")"
  }

  type LEdge[N,L] = EqDiEdge[N] with EdgeCopy[EqDiEdge]
      with OuterEdge[N,EqDiEdge] { type L1 = L }

  implicit object EqDiEdge extends c.edge.LBase.LEdgeCompanion[EqDiEdge] {

    val nodeSeparator = "~+>"

    def apply[N,L](n1: N, n2: N)(l: L): LEdge[N,L] =
      new EqDiEdge[N](n1, n2) {
        type L1 = L
        var label: L = l
      }

    def apply[N,L](nodes: (N, N), label: L): LEdge[N,L] =
      EqDiEdge(nodes._1, nodes._2)(label)

    def apply[N,L](nodes: Iterable[N], label: L): LEdge[N,L] = {
      require(nodes.size == 2,
        "cannot create an edge with more than two endpoints")
      val ns = nodes.iterator
      EqDiEdge(ns.next, ns.next)(label)
    }
  }
    
  type Edge = EqDiEdge[Node]

  final implicit class NodeToEdge[N](n1: N) {
    def ~+>[L](n2: N)(label: L) = EqDiEdge(n1, n2)(label)
    // RHZ: Should this return an edge with label Nothing?
    def ~>(n2: N) = EqDiEdge(n1, n2)("")
  }

  object :~> {
    def unapply[N](e: EqDiEdge[N]): Option[(N, (N, e.L1))] =
      if (e eq null) None else Some((e._1, (e._2, e.label)))
  }

  object + {
    def unapply[N,L](nl: (N, L)): Option[(N, L)] =
      if (nl eq null) None else Some((nl._1, nl._2))
  }


  // --- Arrows and spans ---

  abstract class PInj[N1, E1[X] <: EqDiEdge[X],
                      N2, E2[X] <: EqDiEdge[X]] {

    type Src <: c.mutable.Graph[N1,E1]
    type Tgt <: c.mutable.Graph[N2,E2]

    val dom: Src
    val cod: Tgt

    // IDEA: vals or methods? better names?
    val fn: Map[dom.NodeT, cod.NodeT]
    val fe: Map[dom.EdgeT, cod.EdgeT]

    def inverse = PInj[N2,E2,N1,E1](cod, dom)(
      fn map (_.swap), fe map (_.swap))

    /** Check if this arrow is injective. */
    def isInjective: Boolean =
      fn.values.toSeq.combinations(2).forall { case Seq(n1, n2) => n1 != n2 } &&
      fe.values.toSeq.combinations(2).forall { case Seq(e1, e2) => e1 != e2 }

    /** Check if this arrow is structure-preserving. */
    def isHomomorphic: Boolean =
      fe.keys.forall(e =>
        !(fn.isDefinedAt(e.source) &&
          fn.isDefinedAt(e.target)) ||
        fn(e.source) == fe(e).source &&
        fn(e.target) == fe(e).target)

    /** Check if this arrow is total. */
    def isTotal: Boolean =
      dom.nodes.forall(fn.isDefinedAt(_)) &&
      dom.edges.forall(fe.isDefinedAt(_))

    def apply(u: dom.NodeT): cod.NodeT = fn(u)
    def apply(e: dom.EdgeT): cod.EdgeT = fe(e)

    def className: String = "PartialInjection"

    override def toString =
      className + "(" + (fn mkString ", ") +
      (if (fn.nonEmpty && fe.nonEmpty) ", " else "") +
      (fe mkString ", ") + ")"
  }

  object PInj {

    def apply[N1, E1[X] <: EqDiEdge[X], N2, E2[X] <: EqDiEdge[X]](
      from: c.mutable.Graph[N1,E1],
      to:   c.mutable.Graph[N2,E2])(
      nodeMap: Map[from.NodeT, to.NodeT],
      edgeMap: Map[from.EdgeT, to.EdgeT]) = {
      val p = new PInj[N1,E1,N2,E2] {
        type Src = from.type
        type Tgt = to.type
        val dom: Src = from
        val cod: Tgt = to
        val fn = nodeMap
        val fe = edgeMap
      }
      require(p.isInjective,
        "given node or edge maps are not injective")
      require(p.isHomomorphic,
        "given node or edge maps are not structure-preserving")
      p
    }

    def empty[N1, E1[X] <: EqDiEdge[X], N2, E2[X] <: EqDiEdge[X]](
      implicit tag1: TypeTag[E1[N1]], tag2: TypeTag[E2[N2]]) =
      new PInj[N1,E1,N2,E2] {
        type Src = c.mutable.Graph[N1,E1]
        type Tgt = c.mutable.Graph[N2,E2]
        val dom = Graph.empty[N1,E1](tag1)
        val cod = Graph.empty[N2,E2](tag2)
        val fn = Map.empty[dom.NodeT,cod.NodeT]
        val fe = Map.empty[dom.EdgeT,cod.EdgeT]
      }
  }

  type PartialInjection = PInj[Node,EqDiEdge,Node,EqDiEdge]

  object PartialInjection {
    def apply(from: Graph, to: Graph)(
      nodeMap: Map[from.NodeT, to.NodeT],
      edgeMap: Map[from.EdgeT, to.EdgeT]) =
      PInj[Node,EqDiEdge,Node,EqDiEdge](from, to)(nodeMap, edgeMap)

    def empty = new PartialInjection {
      type Src = Graph
      type Tgt = Graph
      val dom = Graph.empty[Node,EqDiEdge]
      val cod = Graph.empty[Node,EqDiEdge]
      val fn = Map.empty[dom.NodeT,cod.NodeT]
      val fe = Map.empty[dom.EdgeT,cod.EdgeT]
    }
  }


  abstract class Inj[N1, E1[X] <: EqDiEdge[X],
                     N2, E2[X] <: EqDiEdge[X]]
      extends PInj[N1,E1,N2,E2] {
    override def className: String = "Match"
  }

  object Inj {

    def apply[N1, E1[X] <: EqDiEdge[X], N2, E2[X] <: EqDiEdge[X]](
      from: c.mutable.Graph[N1,E1],
      to:   c.mutable.Graph[N2,E2])(
      nodeMap: Map[from.NodeT, to.NodeT],
      edgeMap: Map[from.EdgeT, to.EdgeT]) = {
      val m = new Inj[N1,E1,N2,E2] {
        type Src = from.type
        type Tgt = to.type
        val dom: Src = from
        val cod: Tgt = to
        val fn = nodeMap
        val fe = edgeMap
      }
      require(m.isInjective,
        "given node or edge maps are not injective")
      require(m.isHomomorphic,
        "given node or edge maps are not structure-preserving: " + m)
      require(m.isTotal, "given node or edge maps are not total")
      m
    }

    def empty[N1, E1[X] <: EqDiEdge[X], N2, E2[X] <: EqDiEdge[X]](
      implicit tag1: TypeTag[E1[N1]], tag2: TypeTag[E2[N2]]) =
      new Inj[N1,E1,N2,E2] {
        type Src = c.mutable.Graph[N1,E1]
        type Tgt = c.mutable.Graph[N2,E2]
        val dom = Graph.empty[N1,E1](tag1)
        val cod = Graph.empty[N2,E2](tag2)
        val fn = Map.empty[dom.NodeT,cod.NodeT]
        val fe = Map.empty[dom.EdgeT,cod.EdgeT]
      }
  }

  type Injection = Inj[Node,EqDiEdge,Node,EqDiEdge]

  object Injection {

    def apply(from: Graph, to: Graph)(
      nodeMap: Map[from.NodeT, to.NodeT],
      edgeMap: Map[from.EdgeT, to.EdgeT]) =
      Inj[Node,EqDiEdge,Node,EqDiEdge](from, to)(nodeMap, edgeMap)

    def empty = new Injection {
      type Src = Graph
      type Tgt = Graph
      val dom = Graph.empty[Node,EqDiEdge]
      val cod = Graph.empty[Node,EqDiEdge]
      val fn = Map.empty[dom.NodeT,cod.NodeT]
      val fe = Map.empty[dom.EdgeT,cod.EdgeT]
    }
  }

  type Match = Injection
  val  Match = Injection

  val observables: Seq[Graph] = List()
  val matches = Map[Graph, Seq[Match]]()


  // --- Intersections and Unions ---

  /** Intersections of subobjects of `g1` and `g2`.
    *
    * @return the set of graph intersections with their respective
    *         product injections.
    */
  def intersections(g1: Graph, g2: Graph)
      : Seq[(Graph, Match { type Tgt = g1.type }, Match { type Tgt = g2.type })] = {

    val g1nodes: Seq[g1.NodeT] = g1.nodes.toSeq
    val g2nodes: Seq[g2.NodeT] = g2.nodes.toSeq

    // set of nodes in `g2` indexed by nodes in `g1` that match
    val nodeMatches: Map[g1.NodeT, Seq[g2.NodeT]] = {
      for (n1 <- g1nodes)
      yield (n1, g2nodes filter (n1 =~= _))
    }.toMap

    // all possible node intersections
    val nodeIntersections: Seq[Seq[Seq[(g1.NodeT, g2.NodeT)]]] =
      for (i <- 0 to g1nodes.length;
           n1s <- g1nodes.combinations(i))
      yield cross(n1s map nodeMatches) map (n1s zip _)

    // construct intersections
    (for (ns <- nodeIntersections.flatten) yield {

      val g1nodes = ns map (_._1)
      val g2nodes = ns map (_._2)

      // create base graph
      val nodesOut: Seq[Node] = for ((n1, n2) <- ns) yield
        Node("(" + n1.name + "," + n2.name + ")", n1.label)
      val g = Graph[Node,EqDiEdge](nodesOut:_*)

      // Set-product injections
      val i1 = (nodesOut, g1nodes).zipped.toMap
      val i2 = (nodesOut, g2nodes).zipped.toMap

      // collect all edges between nodes in intersection
      val seen1 = mutable.Set[g1.EdgeT]();
      val seen2 = mutable.Set[g2.EdgeT]();
      val edges: Seq[(Edge, g1.EdgeT, g2.EdgeT)] =
        for { u <- nodesOut;
              v <- nodesOut;
              e1 <- i1(u) outgoingTo i1(v);
              e2 <- i2(u) outgoingTo i2(v);
              // TODO: Is e1 and e2 guaranteed to have the same
              // labels on the endpoint nodes?
              if !seen1(e1) && !seen2(e2) && (e1.label == e2.label);
              _ = seen1 += e1
              _ = seen2 += e2
        } yield (EqDiEdge(u, v)(e1.label), e1, e2)

      // add subsets of found edges to intersection
      for (i <- 0 to edges.length;
           es <- edges.combinations(i)) yield {
        // put the new and old edges apart
        val (edgesOut, g1edges, g2edges) = es.unzip3
        // graph with edges
        val h: Graph = g.clone
        // add edges and get inner edges
        val edgesIn: Seq[h.EdgeT] = for (e <- edgesOut) yield
          h.addAndGetLEdge(e.source, e.target)(e.label)
        // inner nodes
        val nodesIn: Seq[h.NodeT] = nodesOut map h.get
        // node maps
        val fn1 = (nodesIn, g1nodes).zipped.toMap
        val fn2 = (nodesIn, g2nodes).zipped.toMap
        // edge maps
        val fe1 = (edgesIn, g1edges).zipped.toMap
        val fe2 = (edgesIn, g2edges).zipped.toMap
        // create the matches
        (h, Match(h, g1)(fn1, fe1), Match(h, g2)(fn2, fe2))
      }
    }).flatten
  }

  /** Unions of subobjects of `g1` and `g2`. */
  def unions(g1: Graph, g2: Graph)
      : Seq[(Graph, Match { type Src = g1.type }, Match { type Src = g2.type })] =
    // This for shows that intersections and unions are in bijection
    for ((pb: Graph,
      // RHZ: Why can't the compiler infer the right types for `fn` and `fe` from `Src` and `Tgt`?
      m1: Match { type Src = pb.type; type Tgt = g1.type;
        val fn: Map[pb.NodeT, g1.NodeT]; val fe: Map[pb.EdgeT, g1.EdgeT] },
      m2: Match { type Src = pb.type; type Tgt = g2.type;
        val fn: Map[pb.NodeT, g2.NodeT]; val fe: Map[pb.EdgeT, g2.EdgeT] }) <-
        intersections(g1, g2)) yield {

      // create union
      val po: Graph = pb.clone
      val baseFn: Map[pb.NodeT, po.NodeT] =
        (pb.nodes, pb.nodes map (po get _.value)).zipped.toMap
      val baseFe: Seq[(pb.EdgeT, po.EdgeT)] =
        pair(pb, po)(pb.edges.toSeq, po.edges.toSet)

      // missing nodes in intersection
      val g1nodes = g1.nodes.toSeq diff m1.fn.values.toSeq
      val g2nodes = g2.nodes.toSeq diff m2.fn.values.toSeq
      // create missing outer nodes
      val n1out: Seq[Node] = for (n1 <- g1nodes) yield
        Node("(" + n1.name + ",)", n1.label)
      val n2out: Seq[Node] = for (n2 <- g2nodes) yield
        Node("(," + n2.name + ")", n2.label)
      // add them to the graph
      po ++= (n1out ++ n2out)
      // create the node maps
      val fn1: Map[g1.NodeT, po.NodeT] =
        (for ((n0, n1) <- m1.fn) yield (n1, baseFn(n0))).toMap ++
          (g1nodes, n1out map po.get).zipped.toMap
      val fn2: Map[g2.NodeT, po.NodeT] =
        (for ((n0, n2) <- m2.fn) yield (n2, baseFn(n0))).toMap ++
          (g2nodes, n2out map po.get).zipped.toMap

      // missing edges in intersection
      val g1edges = g1.edges.toSeq diff m1.fe.values.toSeq
      val g2edges = g2.edges.toSeq diff m2.fe.values.toSeq
      // create missing outer edges
      val e1out = for (e1 <- g1edges) yield
        EqDiEdge(fn1(e1.source).value, fn1(e1.target).value)(e1.label)
      val e2out = for (e2 <- g2edges) yield
        EqDiEdge(fn2(e2.source).value, fn2(e2.target).value)(e2.label)
      // add them to the graph and get inner edges
      val e1in: Seq[po.EdgeT] = for (e <- e1out) yield
        po.addAndGetLEdge(e.source, e.target)(e.label)
      val e2in: Seq[po.EdgeT] = for (e <- e2out) yield
        po.addAndGetLEdge(e.source, e.target)(e.label)
      // create the edge maps
      val fe1: Map[g1.EdgeT, po.EdgeT] =
        (for ((e0, e3) <- baseFe) yield (m1.fe(e0), e3)).toMap ++
          (g1edges, e1in).zipped.toMap
      val fe2: Map[g2.EdgeT, po.EdgeT] =
        (for ((e0, e3) <- baseFe) yield (m2.fe(e0), e3)).toMap ++
          (g2edges, e2in).zipped.toMap

      (po, Match(g1, po)(fn1, fe1), Match(g2, po)(fn2, fe2))
    }

  // def derivableRightUnions[L: ClassTag](g: Graph, r: Rule): Seq[Graph] = {
  //     // : Seq[(Graph, Match { type Src = g.type }, Match { type Src = r.cod.type })] = {
  //   val inv = r.reversed
  //   for {
  //     (pb, m1, m2) <- unions(g, r.cod)
  //     val i = pb.clone
  //     val (nodes, edges) = inv(m2.asInstanceOf[Match {
  //       val dom: inv.dom.type;
  //       val cod: inv.cod.type }])
  //     val delNodes: Seq[pb.NodeT] = nodes diff pb.nodes
  //     val m3 = Match(r.dom, pb)(m2.fn ++ Map(...))
  //     val _ = r(m3)
  //     if i.isIsoTo[L](pb)
  //   } yield i
  // }

  // def relevantLeftUnions(g: Graph, r: Rule): Seq[Graph] = {
  //   List()
  // }

  // def relevantRightUnions(g: Graph, r: Rule): Seq[Graph] = {
  //   List()
  // }


  // --- Equations ---

  /** A class for graph monomials.
    *
    * @param coef numeric coefficient.
    */
  case class Monomial(coef: Double, factors: Vector[Graph], divisors: Vector[Graph]) {
    def * (n: Double) = Monomial(coef * n, factors, divisors)
    def / (n: Double) = Monomial(coef / n, factors, divisors)
    def * (g: Graph) = Monomial(coef, factors :+ g, divisors)
    def / (g: Graph) = Monomial(coef, factors, divisors :+ g)
    def * (m: Monomial) = Monomial(coef * m.coef, factors ++ m.factors, divisors ++ m.divisors)
    def / (m: Monomial) = Monomial(coef / m.coef, factors ++ m.divisors, divisors ++ m.factors)
    def unary_- = Monomial(-coef, factors, divisors)

    def graphs: Seq[Graph] = factors ++ divisors

    @inline private final def conc(g: Graph): String = "[" + g + "]"

    override def toString = coef +
      (if (factors.isEmpty) ""
       else " " + factors.map(conc).mkString(" ")) +
      (if (divisors.isEmpty) ""
       else " / (" + divisors.map(conc).mkString(" ") + ")")
  }

  case class Polynomial(terms: Vector[Monomial]) {
    def + (m: Monomial) = Polynomial(terms :+ m)
    def + (p: Polynomial) = Polynomial(terms ++ p.terms)
    def - (m: Monomial) = Polynomial(terms :+ (m * -1))
    def - (p: Polynomial) = Polynomial(terms ++ (p.terms match {
      case Vector() => Vector()
      case hd +: tl => (hd * -1) +: tl
    }))

    def graphs: Seq[Graph] = terms flatMap (_.graphs)

    def simplify[L: ClassTag]: Polynomial = {
      val coef = mutable.Map.empty[(Vector[Graph], Vector[Graph]), Double]
      for (Monomial(c1, fs1, ds1) <- terms) {
        coef find {
          case ((fs2, ds2), _) =>
            isos(fs1, fs2, ((g, h) => g.isIsoTo[L](h))) &&
            isos(ds1, ds2, ((g, h) => g.isIsoTo[L](h)))
        } match {
          case Some((m, c2)) => coef(m) = c1 + c2
          case None => coef((fs1, ds1)) = c1
        }
      }
      Polynomial((
        for (((fs, ds), c) <- coef
          if (c <= -eps) || (c >= eps))
        yield Monomial(c, fs, ds)).toVector)
    }

    override def toString =
      if (terms.isEmpty) "0"
      else terms.mkString(" + ").replace("+ -", "- ")
  }

  val eps: Double = 1e-16

  object Implicits {
    implicit def numToMonomial(n: Double) =
      Monomial(n, Vector(), Vector())
    implicit def numToPolynomial(n: Double) =
      Polynomial(Vector(numToMonomial(n)))
    implicit def graphToMonomial(g: Graph) =
      Monomial(1, Vector(g), Vector())
    implicit def graphToPolynomial(g: Graph) =
      Polynomial(Vector(graphToMonomial(g)))
    implicit def monomialToPolynomial(m: Monomial) =
      Polynomial(Vector(m))
  }

  import Implicits._

  sealed abstract class Equation
  case class AlgEquation(lhs: Graph, rhs: Polynomial)
      extends Equation {
    override def toString = lhs.toString + " = " + rhs.toString
  }
  case class ODE(lhs: Graph, rhs: Polynomial)
      extends Equation {
    override def toString = "d[" + lhs + "]/dt = " + rhs
  }

  type Eqs = Vector[Equation]

  def printEqs[L: ClassTag](eqs: Eqs) {
    // Split algebraic equations into substitutions and cancellations
    val (ae0, ae1) = eqs.filter(_.isInstanceOf[AlgEquation]) partition {
      case AlgEquation(_, rhs) => rhs.terms.isEmpty }
    val zeros = ae0.map({ case AlgEquation(lhs, _) => lhs }).toSet
    val subs = ae1.map({ case AlgEquation(lhs, rhs) => (lhs, rhs) }).toMap

    var i = 0
    def newName: String = { i += 1; "F" + i }

    val lhss = eqs.collect({ case ODE(lhs, _) => lhs }).toSet

    // Assign names to graphs
    val names: Map[Graph, String] = {
      (for (ODE(lhs, _) <- eqs) yield (lhs, newName)) ++
      // FIXME
      (for (ODE(_, rhs) <- eqs; m <- rhs.terms; g <- m.graphs)
            // if !(zeros contains g) && !(subs contains g) && !(lhss contains g))
       yield (g, newName)) ++
      (for (AlgEquation(_, rhs) <- ae1; m <- rhs.terms; g <- m.graphs)
            // if !(zeros contains g) && !(subs contains g) && !(lhss contains g))
       yield (g, newName)) ++
      (for (AlgEquation(lhs, _) <- ae1) yield (lhs, newName))
    }.toMap

    // Print those names
    for ((g, name) <- names.toSeq.sortBy(_._2.tail.toInt))
      println(name + " := " + g)
    println()

    // println("zeros:")
    // for (z <- zeros) println("  " + z)
    // println()

    // Print the system of diff eqs
    for (ODE(lhs, rhs) <- eqs) {
      print("d" + names(lhs) + " = ")
      for (m <- rhs.terms) {
        if (m.divisors exists (zeros contains _))
          throw new IllegalArgumentException("division by zero")

        if (!(m.factors exists (zeros contains _))) {

          def expand(queue: Vector[(Graph, Boolean)], c: Double,
            factors: Seq[Graph], divisors: Seq[Graph])
              : (Double, Seq[Graph], Seq[Graph]) = queue match {
            case Vector() => (c, factors, divisors)
            case (g, dividing) +: tl =>
              if (subs contains g) {
                val p = subs(g)
                assume(p.terms.length == 1,
                  "I don't know how to handle this yet, ask Ricardo")
                val sub = p.terms.head
                if (sub.factors.nonEmpty)
                  assume(sub.factors(0) ne (g),
                    "something's fishy here: " + g + " ne " + sub)
                if (dividing) { // when dividing
                  expand(tl ++ (sub.factors.map(g => (g, true)) ++ // factors go to the top
                                sub.divisors.map(g => (g, false))), // and divisors to the bottom
                    c / sub.coef, factors, divisors)
                } else {
                  expand(tl ++ (sub.factors.map(g => (g, false)) ++
                                sub.divisors.map(g => (g, true))),
                    c * sub.coef, factors, divisors)
                }
              } else if (dividing) {
                expand(tl, c, factors, divisors :+ g)
              } else {
                expand(tl, c, factors :+ g, divisors)
              }
          }

          val (coef, factors, divisors) = expand(
            m.factors.map(g => (g, false)) ++
            m.divisors.map(g => (g, true)),
            m.coef, Vector(), Vector())

          if (m.coef < 0) print(" - ")
          else print(" + ")
          print(coef.abs)
          for (g <- factors) print(" * " + names(g))
          if (divisors.nonEmpty) {
            print(" / (" + names(divisors.head))
            for (g <- divisors.tail) print(" * " + names(g))
            print(")")
          }
        }
      }
      println()
    }
  }


  // --- Transformers ---

  // def splitConnectedComponents(g: Graph): Option[Polynomial] =
  val splitConnectedComponents: Graph => Option[Polynomial] = (g: Graph) =>
    if (g.isConnected) None
    else Some(Monomial(1.0, g.split.toVector, Vector()))
 // else g.split.foldLeft(1.0: Monomial)(_ * _))


  // --- Fragmentation ---

  val mfaMaxIter: Int = 30

  def mfa[L: ClassTag](rules: Seq[Rule], observables: Seq[Graph],
    transformers: (Graph => Option[Polynomial])*): Eqs =
    mfa[L](mfaMaxIter, rules, observables, transformers: _*)

  def mfa[L: ClassTag](maxIter: Int, rules: Seq[Rule], observables: Seq[Graph],
    transformers: (Graph => Option[Polynomial])*): Eqs = {

    val reversedRules = rules.map(r => (r, r.reversed)).toMap
    val seen = mutable.ArrayBuffer.empty[Graph]

    @tailrec
    def loop(i: Int, obss: Seq[Graph], eqs: Eqs): Eqs =
      if (i > maxIter) eqs
      else obss match {
        case Seq() => eqs
        case hd +: tl => seen find (hd.isIsoTo[L](_)) match {
          case Some(g) => {
            println(AlgEquation(hd, 1.0 * g))
            if (hd == g) loop(i, tl, eqs)
            else loop(i, tl, eqs :+ AlgEquation(hd, 1.0 * g))
          }
          case None => {
            val ps: Seq[Polynomial] = transformers flatMap (f => f(hd))
            require(ps.length <= 1, "two or more possible transformations of " + hd)
            if (ps.length == 1) {
              // add algebraic equation provided by the transformation
              val p = ps.head
              val eq = AlgEquation(hd, p.simplify[L])
              println(eq)
              seen += hd
              loop(i, tl ++ p.graphs, eqs :+ eq)
            } else {
              // no transformation is aplicable to hd
              val p = Polynomial((for (r <- rules) yield {
                val ropp: Rule = reversedRules(r)
                // minimal glueings with the left-hand side
                val deletions: Seq[Monomial] =
                  for ((mg, _, _) <- unions(hd, r.lhs)) yield -1.0 * r.rate * mg
                // minimal glueings with the right-hand side
                val additions: Seq[Monomial] =
                  for ((mg, _, m) <- unions(hd, ropp.dom)) yield {
                    ropp(m)
                    r.rate * mg
                  }
                deletions ++ additions
              }).flatten.toVector).simplify[L]
              println(ODE(hd, p))
              seen += hd
              loop(i+1, tl ++ p.graphs, eqs :+ ODE(hd, p))
            }
          }
        }
      }

    loop(0, observables, Vector())
  }


  // --- Rules ---

  type Rate = Double

  // TODO: Perhaps there should be `Action`s: `Rule`s without a `Rate`
  abstract class GenRule[N1, E1[X] <: EqDiEdge[X],
                         N2, E2[X] <: EqDiEdge[X]]
      extends PInj[N1,E1,N2,E2] {
    self =>

    type SrcNode = N1
    type TgtNode = N2

    val rate: Rate = 1.0

    /** The left-hand side of the rule, ie what is needed for the rule
      * to be triggered.
      */
    @inline final def lhs: Src = dom

    /** The right-hand side of the rule, ie the result of applying the
      * rule.
      */
    @inline final def rhs: Tgt = cod

    /** `true` if this rule is atomic, that is, if it only creates or
      *  destroys one node or edge (but not both) at a time.
      */
    def isAtomic: Boolean = false

    /** `true` if this rule is a composition of atomic rules
      * (see `isAtomic`).
      */
    @inline final def isComposite: Boolean = !isAtomic

    /** Rewrites the codomain of `m` according to this rule.
      *
      * @param m match that defines where to apply the rule.
      * @return the collection of modified nodes and edges.
      */
    def apply(m: Inj[N1,E1,Node,EqDiEdge] { val dom: self.dom.type })
        : (Set[m.cod.NodeT], Set[m.cod.EdgeT])

    /** The reversed rule. */
    def reversed: GenRule[N2,E2,N1,E1]

    override def className: String = "Rule"

    override def toString = className + "(" + lhs + " -> " + rhs + ")"
  }

  type Rule = GenRule[Node,EqDiEdge,Node,EqDiEdge]


  // -- Atomic rules (a.k.a. actions) --

  sealed abstract class AtomicRule[N1, E1[X] <: EqDiEdge[X],
                                   N2, E2[X] <: EqDiEdge[X]]
      extends GenRule[N1,E1,N2,E2] {
    override def isAtomic = true
  }

  private val rng = util.Random
  var maxRndInt: Int = 10000

  case class AddNode(node: Node)
      extends AtomicRule[Node,EqDiEdge,Node,EqDiEdge] {
    self =>
    type Src = Graph
    type Tgt = Graph
    val dom = Graph[Node,EqDiEdge]()
    val cod = Graph[Node,EqDiEdge](node)
    val fn = Map[dom.NodeT, cod.NodeT]()
    val fe = Map[dom.EdgeT, cod.EdgeT]()
    def randomNode = Node(node.label.toLowerCase +
      rng.nextInt(maxRndInt), node.label)
    // RHZ: This method actually doesn't use the match `m` at all.
    def apply(m: Match { val dom: self.dom.type })
        : (Set[m.cod.NodeT], Set[m.cod.EdgeT]) = {
      // FIXME: There's a tiny chance that the chosen name for `n`
      // is the name of a node in `m.cod` in which case the addition
      // won't work.  I should check, using `Node.hashCode` if that
      // node already exists (maybe `m.cod.nodes.findEntry`?).
      val n = randomNode
      m.cod += n
      (Set(m.cod get n), Set())
    }
    override def reversed = DelNode(node)
    override def className = "AddNode"
  }

  case class DelNode(node: Node)
      extends AtomicRule[Node,EqDiEdge,Node,EqDiEdge] {
    self =>
    type Src = Graph
    type Tgt = Graph
    val dom = Graph[Node,EqDiEdge](node)
    val cod = Graph[Node,EqDiEdge]()
    val fn = Map[dom.NodeT, cod.NodeT]()
    val fe = Map[dom.EdgeT, cod.EdgeT]()
    protected[graph_rewriting] val inner: dom.NodeT = dom get node
    def apply(m: Match { val dom: self.dom.type })
        : (Set[m.cod.NodeT], Set[m.cod.EdgeT]) = {
      val image: m.cod.NodeT = m(inner)
      m.cod -= image
      (Set(image), Set())
    }
    override def reversed = AddNode(node)
    override def className = "DelNode"
  }

  case class SetNodeLabel(n1: Node, n2: Node)
      extends AtomicRule[Node,EqDiEdge,Node,EqDiEdge] {
    self =>
    @inline private final def l1 = n1.label
    @inline private final def l2 = n2.label
    type Src = Graph
    type Tgt = Graph
    val dom = Graph[Node,EqDiEdge](n1)
    val cod = Graph[Node,EqDiEdge](n2)
    val fn = Map(inner -> (cod get n2))
    val fe = Map.empty[dom.EdgeT, cod.EdgeT]
    private val inner: dom.NodeT = dom get n1
    def apply(m: Match { val dom: self.dom.type })
        : (Set[m.cod.NodeT], Set[m.cod.EdgeT]) = {
      val image: m.cod.NodeT = m(inner)
      image.label = l2
      (Set(image), Set())
    }
    override def reversed = SetNodeLabel(n2, n1)
    override def className = "SetNodeLabel"
  }

  case class AddEdge[N: TypeTag](edge: EqDiEdge[N])
      extends AtomicRule[N,EqDiEdge,N,EqDiEdge] {
    self =>
    @inline final private def n1 = edge.source
    @inline final private def n2 = edge.target
    type Src = c.mutable.Graph[N,EqDiEdge]
    type Tgt = c.mutable.Graph[N,EqDiEdge]
    val dom = Graph[N,EqDiEdge](n1, n2)
    val cod = Graph[N,EqDiEdge](edge)
    val fn = Map(source -> (cod get n1),
                 target -> (cod get n2))
    val fe = Map[dom.EdgeT, cod.EdgeT]()
    protected[graph_rewriting] val source: dom.NodeT = dom get n1
    protected[graph_rewriting] val target: dom.NodeT = dom get n2
    def apply(m: Inj[N,EqDiEdge,Node,EqDiEdge] { val dom: self.dom.type })
        : (Set[m.cod.NodeT], Set[m.cod.EdgeT]) = {
      // FIXME: What if one of the nodes doesn't exist on the lhs?
      val s: m.cod.NodeT = m(source)
      val t: m.cod.NodeT = m(target)
      val e: m.cod.EdgeT = m.cod.addAndGetLEdge(s, t)(edge.label)
      (Set(s, t), Set(e))
    }
    override def reversed = DelEdge(edge)
    override def className = "AddEdge[" + typeTag[N].tpe + "]"
  }

  case class AddEdgeToNewNode[N: TypeTag](edge: EqDiEdge[N])
      extends AtomicRule[N,EqDiEdge,N,EqDiEdge] {
    self =>
    @inline final private def n1 = edge.source
    @inline final private def n2 = edge.target
    type Src = c.mutable.Graph[N,EqDiEdge]
    type Tgt = c.mutable.Graph[N,EqDiEdge]
    val dom = Graph[N,EqDiEdge](n1, n2)
    val cod = Graph[N,EqDiEdge](edge)
    val fn = Map(source -> (cod get n1),
                 target -> (cod get n2))
    val fe = Map[dom.EdgeT, cod.EdgeT]()
    protected[graph_rewriting] val source: dom.NodeT = dom get n1
    protected[graph_rewriting] val target: dom.NodeT = dom get n2
    def apply(m: Inj[N,EqDiEdge,Node,EqDiEdge] { val dom: self.dom.type })
        : (Set[m.cod.NodeT], Set[m.cod.EdgeT]) =
      throw new UnsupportedOperationException("apply method in " +
        "AddEdgeToNewNode needs extra argument")
    def apply(m: Inj[N,EqDiEdge,Node,EqDiEdge] { val dom: self.dom.type })(
      to: m.cod.NodeT): (Set[m.cod.NodeT], Set[m.cod.EdgeT]) = {
      val s: m.cod.NodeT = m(source)
      val e: m.cod.EdgeT = m.cod.addAndGetLEdge(s, to)(edge.label)
      (Set(s, to), Set(e))
    }
    override def reversed = DelEdge(edge)
    override def className = "AddEdgeToNewNode[" + typeTag[N].tpe + "]"
  }

  case class AddEdgeFromNewNode[N: TypeTag](edge: EqDiEdge[N])
      extends AtomicRule[N,EqDiEdge,N,EqDiEdge] {
    self =>
    @inline final private def n1 = edge.source
    @inline final private def n2 = edge.target
    type Src = c.mutable.Graph[N,EqDiEdge]
    type Tgt = c.mutable.Graph[N,EqDiEdge]
    val dom = Graph[N,EqDiEdge](n1, n2)
    val cod = Graph[N,EqDiEdge](edge)
    val fn = Map(source -> (cod get n1),
                 target -> (cod get n2))
    val fe = Map[dom.EdgeT, cod.EdgeT]()
    protected[graph_rewriting] val source: dom.NodeT = dom get n1
    protected[graph_rewriting] val target: dom.NodeT = dom get n2
    def apply(m: Inj[N,EqDiEdge,Node,EqDiEdge] { val dom: self.dom.type })
        : (Set[m.cod.NodeT], Set[m.cod.EdgeT]) =
      throw new UnsupportedOperationException("apply method in " +
        "AddEdgeFromNewNode needs extra argument")
    def apply(m: Inj[N,EqDiEdge,Node,EqDiEdge] { val dom: self.dom.type })(
      from: m.cod.NodeT): (Set[m.cod.NodeT], Set[m.cod.EdgeT]) = {
      val t: m.cod.NodeT = m(target)
      val e: m.cod.EdgeT = m.cod.addAndGetLEdge(from, t)(edge.label)
      (Set(from, t), Set(e))
    }
    override def reversed = DelEdge(edge)
    override def className = "AddEdgeFromNewNode[" + typeTag[N].tpe + "]"
  }

  case class DelEdge[N: TypeTag](edge: EqDiEdge[N])
      extends AtomicRule[N,EqDiEdge,N,EqDiEdge] {
    self =>
    @inline final private def n1 = edge.source
    @inline final private def n2 = edge.target
    type Src = c.mutable.Graph[N,EqDiEdge]
    type Tgt = c.mutable.Graph[N,EqDiEdge]
    val dom = Graph[N,EqDiEdge](edge)
    val cod = Graph[N,EqDiEdge](n1, n2)
    val fn = Map((dom get n1) -> (cod get n1),
                 (dom get n2) -> (cod get n2))
    val fe = Map[dom.EdgeT, cod.EdgeT]()
    protected[graph_rewriting] val inner: dom.EdgeT = dom.edges.head
    def apply(m: Inj[N,EqDiEdge,Node,EqDiEdge] { val dom: self.dom.type })
        : (Set[m.cod.NodeT], Set[m.cod.EdgeT]) = {
      val image: m.cod.EdgeT = m(inner)
      m.cod.edges.remove(image)
      (Set(), Set(image))
    }
    override def reversed = AddEdge(edge)
    override def className = "DelEdge[" + typeTag[N].tpe + "]"
  }

  case class SetEdgeLabel[N1: TypeTag, N2: TypeTag, L](
    // FIXME: For some reason it doesn't work if I ask the edges
    // to have labels of type L.
    e1: EqDiEdge[N1], // { type L1 = L }, // LEdge[N1,L],
    e2: EqDiEdge[N2]) // { type L1 = L }) // LEdge[N2,L])
      extends AtomicRule[N1,EqDiEdge,N2,EqDiEdge] {
    self =>
    @inline private final def l1 = e1.label
    @inline private final def l2 = e2.label
    type Src = c.mutable.Graph[N1,EqDiEdge]
    type Tgt = c.mutable.Graph[N2,EqDiEdge]
    val dom = Graph(e1)
    val cod = Graph(e2)
    protected[graph_rewriting] val inner1: dom.EdgeT = dom.edges.head
    protected[graph_rewriting] val inner2: cod.EdgeT = cod.edges.head
    val fn = Map(inner1.source -> inner2.source,
                 inner1.target -> inner2.target)
    val fe = Map(inner1 -> inner2)
    def apply(m: Inj[N1,EqDiEdge,Node,EqDiEdge] { val dom: self.dom.type })
        : (Set[m.cod.NodeT], Set[m.cod.EdgeT]) = {
      val image: m.cod.EdgeT = m(inner1)
      // FIXME: This allows funky stuff to happen like assigning an
      // Int to a String and the result is a String containing the
      // string representation of the number.
      image.edge.asInstanceOf[EqDiEdge[_] { type L1 = L }].label =
        l2.asInstanceOf[L]
      (Set(), Set(image))
    }
    override def reversed = SetEdgeLabel(e2, e1)
    override def className = "SetEdgeLabel[" + typeTag[N1].tpe +
      "," + typeTag[N2].tpe + "]"
  }

  // -- Composite rules --

  abstract class CompositeRule[L: ClassTag] extends Rule {
    self =>

    // RHZ: I gave up using types

    // type S = ( r.type, PInj[Node,EqDiEdge,N,EqDiEdge] {
    //   val dom: self.dom.type; val cod: r.dom.type } )
    //     forSome { type N;
    //               type R <: GenRule[N,EqDiEdge,_,EqDiEdge];
    //               val r: R }

    // /** Sequence of (atomic) rules that compose this rule together
    //   * with the map restrictions (`PartialInjection`s) necessary to
    //   * map the match to the subrule.
    //   */
    // val subrules: Seq[S]

    // val addEdgesToNewNode: Seq[(AddEdgeToNewNode[N],
    //   PInj[Node,EqDiEdge,N,EqDiEdge]) forSome { type N }] = Seq()
    // val addEdgesFromNewNode: Seq[(AddEdgeFromNewNode[N],
    //   PInj[Node,EqDiEdge,N,EqDiEdge]) forSome { type N }] = Seq()

    // def restrict[N, R <: GenRule[N,EqDiEdge,_,EqDiEdge]](r: R)(
    // def restrict[N](r: GenRule[N,EqDiEdge,_,EqDiEdge])(
    //   p: PInj[Node,EqDiEdge,N,EqDiEdge] { val dom: self.dom.type;
    //                                       val cod: r.dom.type },
    //   m: Match { val dom: self.dom.type }) =
    //   new Inj[N,EqDiEdge,Node,EqDiEdge] {
    //     type Src = r.dom.type
    //     type Tgt = m.cod.type
    //     val dom: Src = r.dom
    //     val cod: Tgt = m.cod
    //     val fn: Map[r.dom.NodeT, m.cod.NodeT] = (for ((u, v) <- m.fn; w <- p.fn get u) yield (w, v)).toMap
    //     val fe: Map[r.dom.EdgeT, m.cod.EdgeT] = (for ((e, f) <- m.fe; g <- p.fe get e) yield (g, f)).toMap
    //   }

    // /** Rewrites the codomain of `m` according to this rule.
    //   *
    //   * @param m match that defines where to apply the rule.
    //   * @return the collection of modified nodes and edges.
    //   */
    // def apply(m: Match { val dom: self.dom.type })
    //     : (Seq[m.cod.NodeT], Seq[m.cod.EdgeT]) =
    //   concatPairs(for ((r, p) <- subrules) yield {
    //     // FIXME: Remove ugly type cast
    //     r(restrict(r)(p.asInstanceOf[PInj[Node,EqDiEdge,r.SrcNode,
    //       EqDiEdge] { val dom: self.dom.type; val cod: r.dom.type }],
    //       m)).asInstanceOf[(Seq[m.cod.NodeT], Seq[m.cod.EdgeT])]
    //     //
    //     // RHZ: This didn't work :(
    //     // type N1 = s._1.SrcNode
    //     // val r1: GenRule[N1,EqDiEdge,_,EqDiEdge] = s._1
    //     // val p: PInj[Node,EqDiEdge,N1,EqDiEdge] { val dom: self.dom.type; val cod: r1.dom.type } = s._2 //.asInstanceOf[
    //     //   PInj[Node,EqDiEdge,N,EqDiEdge] { val dom: self.dom.type; val cod: r.dom.type }]
    //     // r(restrict(r)(p, m))
    //     //
    //     // And neither this:
    //     // val (r, p): S = s
    //     // r(restrict[r.SrcNode,r.type](r)(p, m))
    //   })

    val addNodes: Seq[Node]
    val addEdges: Seq[(dom.NodeT, dom.NodeT, L)]
    val delNodes: Seq[dom.NodeT]
    val delEdges: Seq[dom.EdgeT]
    val setNodeLabels: Seq[(dom.NodeT, Label)]
    val setEdgeLabels: Seq[(dom.EdgeT, L)]
    val addEdgesToNewNode: Seq[(dom.NodeT, Int, L)]
    val addEdgesFromNewNode: Seq[(Int, dom.NodeT, L)]
    val addEdgesNewNodes: Seq[(Int, Int, L)]

    def randomNode(n: Node) =
      Node(n.label.toLowerCase + rng.nextInt(maxRndInt), n.label)

    def apply(m: Match { val dom: self.dom.type })
        : (Set[m.cod.NodeT], Set[m.cod.EdgeT]) = {
      val nn = mutable.Map.empty[Int, m.cod.NodeT] // new nodes
      val n1 = for ((n, i) <- addNodes.zipWithIndex) yield {
        // FIXME: There's a tiny chance that the chosen name for `n`
        // is the name of a node in `m.cod` in which case the addition
        // won't work.  I should check, using `Node.hashCode` if that
        // node already exists (maybe `m.cod.nodes.findEntry`?).
        val rndNode = randomNode(n)
        m.cod += rndNode
        val image = m.cod get rndNode
        nn(i) = image
        image
      }
      val (n2, e1) = concatPairs(
        for ((source, target, label) <- addEdges) yield {
          val s = m(source)
          val t = m(target)
          val e = m.cod.addAndGetLEdge(s, t)(label)
          (Set(s, t), Set(e))
        })
      val n3 = for (n <- delNodes) yield {
        val image = m(n)
        m.cod -= image
        image
      }
      val e2 = for (e <- delEdges) yield {
        val image = m(e)
        m.cod.edges.remove(image)
        image
      }
      val n4 = for ((n, label) <- setNodeLabels) yield {
        val image = m(n)
        image.label = label
        image
      }
      val e3 = for ((e, label) <- setEdgeLabels) yield {
        val image: m.cod.EdgeT = m(e)
        image.edge.label match {
          case _: L => image.edge.asInstanceOf[EqDiEdge[_] {
            type L1 = L }].label = label
          case _ => throw new IllegalArgumentException("label " +
              image.edge.label + " of edge " + image.edge +
              " is not of type " + classTag[L])
        }
        image
      }
      val (n5, e4) = concatPairs(
        for ((source, i, label) <- addEdgesToNewNode) yield {
          val s = m(source)
          val t = nn(i)
          val e = m.cod.addAndGetLEdge(s, t)(label)
          (Set(s, t), Set(e))
        })
      val (n6, e5) = concatPairs(
        for ((i, target, label) <- addEdgesFromNewNode) yield {
          val s = nn(i)
          val t = m(target)
          val e = m.cod.addAndGetLEdge(s, t)(label)
          (Set(s, t), Set(e))
        })
      val e6 = for ((i, j, label) <- addEdgesNewNodes) yield {
        val s = nn(i)
        val t = nn(j)
        val e = m.cod.addAndGetLEdge(s, t)(label)
        e
      }
      (n1.toSet ++ n2 ++ n3 ++ n4 ++ n5 ++ n6,
       e1.toSet ++ e2 ++ e3 ++ e4 ++ e5 ++ e6)
    }


    // TODO: I should return a Rule { val dom: cod.type; val cod: dom.type }
    /** The reversed rule. */
    override def reversed =
      Rule(cod, dom)(fn map (_.swap), fe map (_.swap), rate)
  }

  object Rule {

    // def apply[L: ClassTag](lhs: Graph, rhs: Graph, k: Rate): CompositeRule[L] =
    //   apply(lhs, rhs)(
    //     (lhs.nodes, rhs.nodes).zipped.toMap,
    //     (lhs.edges, rhs.edges).zipped.toMap, k)

    def apply[L: ClassTag](leftHandSide: Graph, rightHandSide: Graph)(
      nodeMap: Map[leftHandSide.NodeT, rightHandSide.NodeT],
      edgeMap: Map[leftHandSide.EdgeT, rightHandSide.EdgeT], k: Rate)
        : CompositeRule[L] = {
      val r = new CompositeRule[L] {
        override val rate = k
        type Src = leftHandSide.type
        type Tgt = rightHandSide.type
        val dom: Src = leftHandSide
        val cod: Tgt = rightHandSide
        val fn = nodeMap
        val fe = edgeMap
        // FIXME: Replace by the inverse maps of fn and fe. Read below
        private val nodesImage = fn.values.toSet
        private val edgesImage = fe.values.toSet
        private def labelOf(e: EqDiEdge[_]): L = e.label match {
          case l: L => l
          case l => throw new IllegalArgumentException(
            "edge's label not of type " + classTag[L] + ": " + l)
        }
        val (addNodes, addEdgesToNewNode, addEdgesFromNewNode, addEdgesNewNodes) = {
          var i = 0
          val m = mutable.Map.empty[cod.NodeT, Int]
          (for (n2 <- cod.nodes.toSeq if !(nodesImage contains n2))
           yield {
             m(n2) = i
             val toEdges: Seq[(dom.NodeT, Int, L)] =
               for {
                 e2 <- n2.incoming.toSeq
                 if (nodesImage contains e2.source)
                 // TODO: This whole collectFirst business could be
                 // better handled if nodesImages is a Map instead,
                 // the reverse map of fn.
                 val source = fn collectFirst { case (n1, n2)
                   if n2 == e2.source => n1 }
               } yield (source.get, i, labelOf(e2))
             val fromEdges: Seq[(Int, dom.NodeT, L)] =
               for {
                 e2 <- n2.outgoing.toSeq
                 if (nodesImage contains e2.target)
                 val target = fn collectFirst { case (n1, n2)
                   if n2 == e2.target => n1 }
               } yield (i, target.get, labelOf(e2))
             val newEdges: Seq[(Int, Int, L)] =
               (for {
                 e2 <- n2.incoming.toSeq
                 if !(nodesImage contains e2.source)
                 if (m contains e2.source)
                 val j = m(e2.source)
               } yield (j, i, labelOf(e2))) ++
             (for {
               e2 <- n2.edges.toSeq
               if !(nodesImage contains e2.target)
               if (m contains e2.target)
               val j = m(e2.target)
             } yield (i, j, labelOf(e2)))
             i += 1
             (n2.value, toEdges, fromEdges, newEdges)
           }).foldRight(
            Seq.empty[Node],
            Seq.empty[(dom.NodeT, Int, L)],
            Seq.empty[(Int, dom.NodeT, L)],
            Seq.empty[(Int, Int, L)])({ case ((a1, a2, a3, a4), (a1s, a2s, a3s, a4s)) =>
              (a1s :+ a1, a2s ++ a2, a3s ++ a3, a4s ++ a4) })
        }
        val addEdges: Seq[(dom.NodeT, dom.NodeT, L)] =
          for {
            e2 <- cod.edges.toSeq
            if !(edgesImage contains e2)
            val source = fn collectFirst { case (n1, n2)
              if n2 == e2.source => n1 }
            val target = fn collectFirst { case (n1, n2)
              if n2 == e2.target => n1 }
            if (source.isDefined && target.isDefined)
          } yield (source.get, target.get, labelOf(e2))
        val delNodes: Seq[dom.NodeT] =
          for (n1 <- dom.nodes.toSeq if !(fn contains n1)) yield n1
        val delEdges: Seq[dom.EdgeT] =
          for (e1 <- dom.edges.toSeq if !(fe contains e1)) yield e1
        val setNodeLabels: Seq[(dom.NodeT, Label)] =
          for ((n1, n2) <- fn.toSeq if n1.label != n2.label) yield (n1, n2.label)
        val setEdgeLabels: Seq[(dom.EdgeT, L)] =
          for ((e1, e2) <- fe.toSeq if e1.label != e2.label) yield (e1, labelOf(e2))
        // val subrules: Seq[S] = {
        //   // println("Finding subrules of: " + toString)
        //   val nodesImage = fn.values.toSet
        //   val edgesImage = fe.values.toSet
        //   // -- Updates --
        //   ((for ((n1, n2) <- fn if n1.label != n2.label) yield {
        //     val r = SetNodeLabel(n1.value, n2.value)
        //     // println("  " + r)
        //     (r, PartialInjection(dom, r.dom)(
        //       Map(n1 -> r.dom.get(n1)), Map()))
        //   }).toSeq: Seq[S]) ++
        //   (for ((e1, e2) <- fe if e1.label != e2.label) yield {
        //     // FIXME: This will never happen because this.isHomomorphic
        //     val r = SetEdgeLabel(e1.edge, e2.edge)
        //     // println("  " + r)
        //     (r, PInj(dom, r.dom)(Map(), Map(e1 -> r.inner1)))
        //   }) ++
        //   // -- Deletions --
        //   (for (n1 <- leftHandSide.nodes if !(fn contains n1)) yield {
        //     val r = DelNode(n1)
        //     // println("  " + r)
        //     (r, PartialInjection(dom, r.dom)(
        //       Map(n1 -> r.dom.get(n1)), Map()))
        //    }) ++
        //   (for (e1 <- leftHandSide.edges if !(fe contains e1)) yield {
        //     // RHZ: No TypeTag available for this.dom.NodeT, but
        //     // for leftHandSide.NodeT there is... why?
        //     val r = DelEdge(e1.edge)
        //     // println("  " + r)
        //     (r, PInj(dom, r.dom)(Map(), Map(e1 -> r.inner)))
        //    }) ++
        //   // -- Additions --
        //   (for (n2 <- rightHandSide.nodes if !(nodesImage contains n2)) yield {
        //     val r = AddNode(n2)
        //     // println("  " + r)
        //     (r, PartialInjection(dom, r.dom)(Map(), Map()))
        //   }) ++
        //   (for (e2 <- rightHandSide.edges if !(edgesImage contains e2)) yield {
        //     val r = AddEdge(e2.edge)
        //     // println("  " + r)
        //     val source = fn collectFirst { case (n1, n2)
        //       if n2 == e2.source => n1 }
        //     val target = fn collectFirst { case (n1, n2)
        //       if n2 == e2.target => n1 }
        //     // FIXME: If one of the nodes does not exist in the lhs
        //     // we will get an exception here.
        //     require(source.isDefined, "source node of " + e2 + " is not in the lhs")
        //     require(target.isDefined, "target node of " + e2 + " is not in the lhs")
        //     (r, PInj(dom, r.dom)(
        //       Map(source.get -> r.source,
        //           target.get -> r.target), Map()))
        //   })
        // }.toSeq
      }
      require(r.isInjective,
        "given node or edge maps are not injective")
      require(r.isHomomorphic,
        "given node or edge maps are not structure-preserving")
      r
    }
  }

  val rules: Seq[Rule] = List()


  // --- State ---

  type State = Graph
  val state: State = Graph[Node, EqDiEdge]()

  var time: Double = 0.0
  var events: Long = 0
  var _maxTime: Option[Double] = None
  var _maxEvents: Option[Long] = None

  /** Set the maximum time for the simulation. */
  def maxTime_=(t: Double) = { _maxTime = Some(t) }
  @inline def maxTime = _maxTime

  /** Set the maximum number of events for the simulation. */
  def maxEvents_=(e: Long) = { _maxEvents = Some(e) }
  @inline def maxEvents = _maxEvents

  // Create a new random number generator
  val rand = new util.Random

  /** Pick a random element of the sequence. */
  def randomElement[A](xs: Seq[A]): A =
    xs(rand.nextInt(xs.length))

  /** Simulate. */
  def run {

    // Main loop
    while ((events < (maxEvents getOrElse (events + 1))) &&
           (time < (maxTime getOrElse Double.PositiveInfinity))) {

      // Compute rule propensities
      val propensities = for (r <- rules) yield
        (r.rate * matches(r.lhs).length)

      // Build the propensity tree
      val tree = RandomTree(propensities, rand)
      val totalProp = tree.totalWeight

      if (totalProp == 0 || totalProp.isNaN)
        throw new IllegalStateException("no more events")
      
      // Advance time
      val dt = -math.log(rand.nextDouble) / totalProp
      time += dt

      // Pick a rule and event at random
      val r = rules(tree.nextRandom)
      val e = randomElement(matches(r.lhs))

      // Apply the rule/event
      // ...
    }
  }
}

