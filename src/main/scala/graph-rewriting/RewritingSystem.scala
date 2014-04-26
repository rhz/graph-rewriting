package graph_rewriting

// import scala.reflect.runtime.universe.TypeTag
import scala.collection.mutable
import mutable.ArrayBuffer

import scalax.{collection => c}
import c.GraphEdge._ // EdgeCopy,...
import c.GraphPredef._ // OuterEdge,Param


// abstract class RewritingSystem {
object RewritingSystem {

  type Edge = EqDiEdge[Node]
  type Graph = c.mutable.Graph[Node, EqDiEdge]
  type Label = String


  // --- Graphs ---

  // import Graph companion object
  val Graph = c.mutable.Graph

  implicit final class ComparableGraph(g: Graph) {
    def =~=(that: Graph): Boolean = {
      if (!g.isConnected || !that.isConnected)
        throw new IllegalArgumentException(
          "given graphs must be connected")
      (g.nodes.length == that.nodes.length) &&
      (g.edges.length == that.edges.length)
      // To do the traversal I must follow successors and predecessors
    }
  }


  // --- Nodes ---

  /** Node class.
    *
    * @param name name of the node.
    * @param label label of the node.
    */
  final case class Node(name: String, label: Label) {

    def matches(that: Node): Boolean = this.label == that.label

    override def toString = "\"" + name + // ":" + label + "\""
      (if (label.isEmpty) "" else ":" + label) + "\""

    override def equals(that: Any) = that match {
      case Node(nme,_) => this.name == nme
      case _ => false
    }

    override def canEqual(that: Any) = that.isInstanceOf[Node]

    override def hashCode = name.hashCode
  }

  private val nodeRegex = "([^,:]*)(:[^,:]*)?".r

  implicit def node(s: String) = s match {
    case nodeRegex(name, null)  => Node(name, "")
    case nodeRegex(name, label) => Node(name, label.tail)
    case _ => throw new IllegalArgumentException("illegal string " +
        "for a node: '" + s + "' doesn't conform to regex " +
        nodeRegex)
  }


  // --- (Multi-)Edges ---

  /** Labelled directed multi-edge.
    *
    * @tparam N the type of nodes.
    * @param label label of the edge.
    */
  class EqDiEdge[N](nodes: Product, override val label: Label)
      extends c.edge.LDiEdge[N](nodes)
         with EdgeCopy[EqDiEdge]
         with OuterEdge[N,EqDiEdge] {

    type L1 = Label

    override def copy[N](newNodes: Product) =
      new EqDiEdge[N](newNodes, label)
    
    override def equals(other: Any) = other match {
      case that: EqDiEdge[_] => this eq that
      case _ => false
    }

    override def hashCode: Int = {
      val h = System.identityHashCode(this)
      (h << 1) - (h << 8) // for optimized hash distribution
      // nodes.hashCode ^ label.hashCode
    }

    def matches(that: EdgeLike[_]): Boolean =
      this.label == that.label

    // FIXME: For some strange reason this relation is not
    // symmetric when using an inner edge and an outer edge:
    // (in =~= out) is true, but (out =~= in) is not
    def =~=(that: EdgeLike[_]): Boolean =
      matches(that) && baseEquals(that)

    override protected def nodesToStringSeparator =
      EqDiEdge.nodeSeparator

    override protected def attributesToString =
      " (\"" + label + "\")"

    override protected def nodesToString =
      "(" + super.nodesToString + ")"
  }

  implicit object EqDiEdge extends c.edge.LBase.LEdgeCompanion[EqDiEdge] {

    val nodeSeparator = "~+>"
    
    def apply[N](from: N, to: N)(label: Label) =
      new EqDiEdge[N](NodeProduct(from, to), label)

    def apply[N](nodes: (N, N))(label: Label) =
      new EqDiEdge[N](nodes, label)

    def apply[N](nodes: Product)(label: Label) =
      new EqDiEdge[N](nodes, label)
    
    def newEdge[N, L](nodes: Product, label: L) = label match {
      // FIXME: How do you convince the compiler that EqDiEdge
      // implements EdgeCopy and L1 = Label?
      case l: Label => new EqDiEdge[N](nodes, l).asInstanceOf[
        EqDiEdge[N] with EdgeCopy[EqDiEdge] { type L1 = L }]
      case _ => throw new IllegalArgumentException(
        "label type is not String")
    }
  }
    
  // final implicit class NodeToEdge[N](n1: N) {
  //   def ~+>(n2: N)(label: Label) = new EqDiEdge[N]((n1, n2), label)
  // }

  final implicit class NodeToEdge(n1: Node) {
    def ~+>(n2: Node)(label: Label) = EqDiEdge(n1, n2)(label)
    def ~>(n2: Node) = EqDiEdge(n1, n2)("")
  }

  final implicit class StringToEdge(s1: String) {
    val n1 = node(s1)
    def ~+>(s2: String)(label: Label) = EqDiEdge(n1, node(s2))(label)
    def ~>(s2: String) = EqDiEdge(n1, node(s2))("")
  }

  object :~> {
    def unapply[N](e: EqDiEdge[N]): Option[(N, N, Label)] =
      if (e eq null) None else Some((e._1, e._2, e.label))
  }

  object + {
    def unapply[N](nl: (N, Label)): Option[(N, Label)] =
      if (nl eq null) None else Some((nl._1, nl._2))
  }


  // --- Arrows and spans ---

  abstract class PartialInjection {

    type Src <: Graph
    type Tgt <: Graph

    val dom: Src
    val cod: Tgt

    // TODO: vals or methods? better names?
    val fn: Map[dom.NodeT, cod.NodeT]
    val fe: Map[dom.EdgeT, cod.EdgeT]

    def reverse = PartialInjection(cod, dom)(
      fn map (_.swap), fe map (_.swap))

    /** Check if this arrow is injective. */
    def isInjective: Boolean =
      fn.values.toSeq.combinations(2).forall { case Seq(n1, n2) => n1 != n2 } &&
      fe.values.toSeq.combinations(2).forall { case Seq(e1, e2) => e1 != e2 }

    /** Check if this arrow is structure-preserving. */
    def isHomomorphic: Boolean =
      fe.keys.forall(e =>
        fn.isDefinedAt(e.source) &&
        fn.isDefinedAt(e.target) &&
        fn(e.source) == fe(e).source &&
        fn(e.target) == fe(e).target)

    /** Check if this arrow is total. */
    def isTotal: Boolean =
      dom.nodes.forall(fn.isDefinedAt(_)) &&
      dom.edges.forall(fe.isDefinedAt(_))

    // /** Check if this arrow is total. */
    // def isValid: Boolean = isInjective && isHomomorphic

    def apply(u: dom.NodeT): cod.NodeT = fn(u)
    def apply(e: dom.EdgeT): cod.EdgeT = fe(e)

    def className: String = "PartialInjection"

    override def toString =
      className + "(" + (fn mkString ", ") +
      (if (fn.nonEmpty && fe.nonEmpty) ", " else "") +
      (fe mkString ", ") + ")"
  }

  object PartialInjection {

    def apply(from: Graph, to: Graph)(
      nodeMap: Map[from.NodeT, to.NodeT],
      edgeMap: Map[from.EdgeT, to.EdgeT]): PartialInjection = {
      val p = new PartialInjection {
        type Src = from.type
        type Tgt = to.type
        val dom: Src = from
        val cod: Tgt = to
        val fn = nodeMap
        val fe = edgeMap
      }
      if (!p.isInjective) throw new IllegalArgumentException(
        "given node or edge maps are not injective")
      if (!p.isHomomorphic) throw new IllegalArgumentException(
        "given node or edge maps are not structure-preserving")
      p
    }
  }


  abstract class Injection extends PartialInjection {

    // /** Check if this arrow is monic and total. */
    // override def isValid: Boolean =
    //   isInjective && isHomomorphic && isTotal

    override def className: String = "Match"
  }

  object Injection {
    def apply(from: Graph, to: Graph)(
      nodeMap: Map[from.NodeT, to.NodeT],
      edgeMap: Map[from.EdgeT, to.EdgeT]): Injection = {
      val m = new Injection {
        type Src = from.type
        type Tgt = to.type
        val dom: Src = from
        val cod: Tgt = to
        val fn = nodeMap
        val fe = edgeMap
      }
      if (!m.isInjective) throw new IllegalArgumentException(
        "given node or edge maps are not injective")
      if (!m.isHomomorphic) throw new IllegalArgumentException(
        "given node or edge maps are not structure-preserving:\n" + from + "\n" + to + "\n" + nodeMap + "\n" + edgeMap)
      if (!m.isTotal) throw new IllegalArgumentException(
        "given node or edge maps are not total")
      m
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
      : Seq[(Graph, Match, Match)] = {

    val g1nodes: Seq[g1.NodeT] = g1.nodes.toSeq
    val g2nodes: Seq[g2.NodeT] = g2.nodes.toSeq

    // set of nodes in `g2` indexed by nodes in `g1` that match
    val nodeMatches: Map[g1.NodeT, Seq[g2.NodeT]] = {
      for (n1 <- g1nodes)
      yield (n1, g2nodes filter (n1 matches _))
    }.toMap

    // all possible node intersections
    val nodeIntersections: Seq[Seq[Seq[(g1.NodeT, g2.NodeT)]]] =
      for (i <- 0 to g1nodes.length;
           n1s <- g1nodes.combinations(i))
      yield cross(n1s map nodeMatches) map (n1s zip _)

    // construct intersections
    val gs = for (ns <- nodeIntersections.flatten) yield {

      val g1nodes = ns map (_._1)
      val g2nodes = ns map (_._2)

      // create base graph
      val nodesOut = for ((n1, n2) <- ns) yield
        Node(n1.name + "," + n2.name, n1.label)
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
              if !seen1(e1) && !seen2(e2) && (e1 matches e2);
              _ = seen1 += e1
              _ = seen2 += e2
        } yield ((u ~+> v)(e1.label), e1, e2)

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
        // val edgesIn: Seq[h.EdgeT] =
        //   pair(edgesOut, h)(h.edges.to[ArrayBuffer]) map (_._2)
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
    }
    gs.flatten
  }

  /** Pick an element of each sequence non-deterministically. */
  private def cross[A](xss: Seq[Seq[A]], seen: Set[A] = Set[A]())
      : Seq[Seq[A]] = xss match {
    case Seq() => List(List())
    case xs +: xss => for { y <- xs if !seen(y);
                            yss <- cross(xss, seen + y) }
                      yield (y +: yss)
  }

  /** Unions of subobjects of `g1` and `g2`. */
  def unions(g1: Graph, g2: Graph): Seq[(Graph, Match, Match)] =
    // This for shows that intersections and unions are in bijection
    for ((pb,
      m1: Match { type Src = pb.type; type Tgt = g1.type },
      m2: Match { type Src = pb.type; type Tgt = g2.type }) <-
        intersections(g1, g2)) yield {

      // create union
      val po: Graph = pb.clone
      val baseFn: Map[pb.NodeT, po.NodeT] =
        (pb.nodes, pb.nodes map (po get _.value)).zipped.toMap
      val baseFe: Seq[(pb.EdgeT, po.EdgeT)] =
        pair(pb, po)(pb.edges.to[Seq], po.edges.to[ArrayBuffer])

      // val reverse1 = m1.reverse
      // val reverse2 = m2.reverse

      // missing nodes in intersection
      val g1nodes = g1.nodes.toSeq diff m1.fn.values.toSeq
      val g2nodes = g2.nodes.toSeq diff m2.fn.values.toSeq
      // create missing outer nodes
      val n1out: Seq[Node] = for (n1 <- g1nodes) yield
        Node(n1.name + ",", n1.label)
      val n2out: Seq[Node] = for (n2 <- g2nodes) yield
        Node("," + n2.name, n2.label)
      // add them to the graph
      po ++= (n1out ++ n2out)
      // create the node maps
      val fn1: Map[g1.NodeT, po.NodeT] =
        // reverse1.fn.asInstanceOf[Map[g1.NodeT, po.NodeT]] ++
        (for ((n0, n1) <- m1.fn) yield (n1, baseFn(n0))).toMap ++
          (g1nodes, n1out map po.get).zipped.toMap
      val fn2: Map[g2.NodeT, po.NodeT] =
        // reverse2.fn.asInstanceOf[Map[g2.NodeT, po.NodeT]] ++
        (for ((n0, n2) <- m2.fn) yield (n2, baseFn(n0))).toMap ++
          (g2nodes, n2out map po.get).zipped.toMap

      // missing edges in intersection
      val g1edges = g1.edges.toSeq diff m1.fe.values.toSeq
      val g2edges = g2.edges.toSeq diff m2.fe.values.toSeq
      // create missing outer edges
      val e1out = for (e1 <- g1edges) yield
        (fn1(e1.source).value ~+> fn1(e1.target).value)(e1.label)
      val e2out = for (e2 <- g2edges) yield
        (fn2(e2.source).value ~+> fn2(e2.target).value)(e2.label)
      // add them to the graph and get inner edges
      // po ++= (e1out ++ e2out)
      val e1in: Seq[po.EdgeT] = for (e <- e1out) yield
        po.addAndGetLEdge(e.source, e.target)(e.label)
      // val e1in: Seq[po.EdgeT] =
      //   pair(e1out, po)(po.edges.to[ArrayBuffer]) map (_._2)
      val e2in: Seq[po.EdgeT] = for (e <- e2out) yield
        po.addAndGetLEdge(e.source, e.target)(e.label)
      // val e2in: Seq[po.EdgeT] =
      //   pair(e2out, po)(po.edges.to[ArrayBuffer]) map (_._2)
      // create the edge maps
      val fe1: Map[g1.EdgeT, po.EdgeT] =
        // reverse1.fe.asInstanceOf[Map[g1.EdgeT, po.EdgeT]] ++
        // (pb.edges map m1.fe, po.edges).zipped.toMap ++
        (for ((e0, e3) <- baseFe) yield (m1.fe(e0), e3)).toMap ++
          (g1edges, e1in).zipped.toMap
      val fe2: Map[g2.EdgeT, po.EdgeT] =
        // reverse2.fe.asInstanceOf[Map[g2.EdgeT, po.EdgeT]] ++
        // (pb.edges map m2.fe, po.edges).zipped.toMap ++
        (for ((e0, e3) <- baseFe) yield (m2.fe(e0), e3)).toMap ++
          (g2edges, e2in).zipped.toMap

      // TODO: I should put a test with intersections and unions

      (po, Match(g1, po)(fn1, fe1), Match(g2, po)(fn2, fe2))
    }

  // NOTE: This is a new version of pair, look into the git history
  // to find the old one that pairs outer with inner edges
  /** Pair outer and inner edges in a given graph using `=~=`. */
  def pair(g1: Graph, g2: Graph)(
    edges1: Seq[g1.EdgeT],
    edges2: ArrayBuffer[g2.EdgeT]): Seq[(g1.EdgeT, g2.EdgeT)] =
    edges1 match {
      case Seq() => List()
      case e1 +: rest1 => edges2 find (_ =~= e1) match {
        case Some(e2) => (e1, e2) +: pair(g1, g2)(rest1, edges2 - e2)
        case None => throw new IllegalArgumentException(
          "edge " + e1 + " doesn't pair with any edge in " + edges2)
      }
    }

  // def relevantLeftUnions(g: Graph, r: Rule): Seq[Graph] = {
  //   List()
  // }

  // def relevantRightUnions(g: Graph, r: Rule): Seq[Graph] = {
  //   List()
  // }


  // --- Fragmentation ---

  // TODO: I'll need more sophisticated datatypes here to do
  // simplification of terms.
  type Rate = Double
  type Prod = Seq[Graph]
  type Poly = Seq[(Rate, Prod)]
  type ODE = (Graph, Poly)

  def mfa(rules: Seq[Rule], observables: Seq[Graph],
    invariants: Seq[Graph => Graph] = List()): Seq[ODE] = {
    List()
  }


  // --- Rules ---

  abstract class Rule extends PartialInjection {

    val rate: Rate = 1.0

    @inline final def lhs: Graph = dom
    @inline final def rhs: Graph = cod

    def isAtomic: Boolean = false
    @inline final def isComposite: Boolean = !isAtomic

    /** Rewrites the codomain of `m` according to this rule.
      *
      * @param m match that defines where to apply the rule.
      * @return the collection of modified nodes and edges.
      */
    def apply(m: Match): (Seq[m.cod.NodeT], Seq[m.cod.EdgeT])

    override def className: String = "Rule"

    override def toString = className + "(" + lhs + " -> " + rhs + ")"
  }


  // -- Atomic rules (a.k.a. actions) --

  sealed abstract class AtomicRule extends Rule {
    override def isAtomic = true
  }

  // TODO: I should make "1" and "2" vals of type Node
  case class AddNode(node: Node) extends AtomicRule {
    private val n1: Node = "1"
    type Src = Graph
    type Tgt = Graph
    val dom = Graph[Node,EqDiEdge]()
    val cod = Graph[Node,EqDiEdge](n1)
    val fn = Map[dom.NodeT, cod.NodeT]()
    val fe = Map[dom.EdgeT, cod.EdgeT]()
    def apply(m: Match): (Seq[m.cod.NodeT], Seq[m.cod.EdgeT]) =
      (List(), List())
    override def reverse: AtomicRule = DelNode(node)
  }

  case class DelNode(node: Node) extends AtomicRule {
    private val n1: Node = "1"
    type Src = Graph
    type Tgt = Graph
    val dom = Graph[Node,EqDiEdge](n1)
    val cod = Graph[Node,EqDiEdge]()
    val fn = Map[dom.NodeT, cod.NodeT]()
    val fe = Map[dom.EdgeT, cod.EdgeT]()
    def apply(m: Match): (Seq[m.cod.NodeT], Seq[m.cod.EdgeT]) =
      (List(), List())
    override def reverse: AtomicRule = AddNode(node)
  }

  case class AddEdge(edge: Edge) extends AtomicRule {
    private val n1: Node = "1"
    private val n2: Node = "2"
    type Src = Graph
    type Tgt = Graph
    val dom = Graph[Node,EqDiEdge](n1, n2)
    val cod = Graph[Node,EqDiEdge](n1~>n2)
    val fn = Map((dom get n1) -> (cod get n1),
                 (dom get n2) -> (cod get n2))
    val fe = Map[dom.EdgeT, cod.EdgeT]()
    def apply(m: Match): (Seq[m.cod.NodeT], Seq[m.cod.EdgeT]) =
      (List(), List())
    override def reverse: AtomicRule = DelEdge(edge)
  }

  case class DelEdge(edge: Edge) extends AtomicRule {
    private val n1: Node = "1"
    private val n2: Node = "2"
    type Src = Graph
    type Tgt = Graph
    val dom = Graph[Node,EqDiEdge](n1~>n2)
    val cod = Graph[Node,EqDiEdge](n1, n2)
    val fn = Map((dom get n1) -> (cod get n1),
                 (dom get n2) -> (cod get n2))
    val fe = Map[dom.EdgeT, cod.EdgeT]()
    def apply(m: Match): (Seq[m.cod.NodeT], Seq[m.cod.EdgeT]) =
      (List(), List())
    override def reverse: AtomicRule = AddEdge(edge)
  }


  // -- Composite rules --

  abstract class CompositeRule extends Rule {

    /** Sequence of (atomic) rules that compose this rule. */
    val subrules : Seq[Rule]

    /** Rewrites the codomain of `m` according to this rule.
      *
      * @param m match that defines where to apply the rule.
      * @return the collection of modified nodes and edges.
      */
    def apply(m: Match): (Seq[m.cod.NodeT], Seq[m.cod.EdgeT]) =
      collect(for (r <- subrules) yield r(m))

    private def collect[A, B](xys: Seq[(Seq[A], Seq[B])])
        : (Seq[A], Seq[B]) =
      xys.foldLeft((List[A](), List[B]())) {
        case ((xs, ys), (xss, yss)) => (xs ++ xss, ys ++ yss) }

    override def reverse: CompositeRule = Rule(cod, dom)(
      fn map (_.swap), fe map (_.swap), rate)
  }

  object Rule {

    def apply(lhs: Graph, rhs: Graph, k: Rate): CompositeRule =
      apply(lhs, rhs)(
        (lhs.nodes, rhs.nodes).zipped.toMap,
        (lhs.edges, rhs.edges).zipped.toMap, k)

    def apply(leftHandSide: Graph, rightHandSide: Graph)(
      nodeMap: Map[leftHandSide.NodeT, rightHandSide.NodeT],
      edgeMap: Map[leftHandSide.EdgeT, rightHandSide.EdgeT], k: Rate)
        : CompositeRule = {
      val r = new CompositeRule {
        override val rate = k
        type Src = leftHandSide.type
        type Tgt = rightHandSide.type
        val dom: Src = leftHandSide
        val cod: Tgt = rightHandSide
        val fn = nodeMap
        val fe = edgeMap
        val subrules = atomicRules(this)
      }
      if (!r.isInjective) throw new IllegalArgumentException(
        "given node or edge maps are not injective")
      if (!r.isHomomorphic) throw new IllegalArgumentException(
        "given node or edge maps are not structure-preserving")
      r
    }

    def atomicRules(r: Rule): Seq[AtomicRule] = {
      List()
    }
  }

  val rules: Seq[Rule] = List()


  // --- State ---

  type State = c.mutable.Graph[Node, EqDiEdge]
  val state: State = c.mutable.Graph[Node, EqDiEdge]()

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

