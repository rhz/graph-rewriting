package graph_rewriting

// import scala.reflect.runtime.universe.TypeTag
import scala.collection.mutable.ArrayBuffer

import scalax.{collection => c}
import c.GraphEdge._
import c.GraphPredef.OuterEdge


// abstract class RewritingSystem {
object RewritingSystem {

  type Edge = EqDiEdge[Node]
  type Graph = c.Graph[Node, EqDiEdge]
  type Label = String


  // --- Graphs ---

  // import Graph companion object
  val Graph = c.Graph


  // --- Nodes ---

  /** Node class.
    *
    * @param name name of the node.
    * @param label label of the node.
    */
  final case class Node(name: String, label: Label) {

    def matches(that: Node): Boolean = this.label == that.label

    override def toString = "\"" + name +
      (if (label.nonEmpty) ":" + label else "") + "\""

    override def equals(that: Any) = that match {
      case Node(nme,_) => this.name == nme
      case _ => false
    }

    override def canEqual(that: Any) = that.isInstanceOf[Node]

    override def hashCode = name.hashCode
  }

  implicit def strToNode(s: String) =
    s count (_ == ':') match {
      case 0 => Node(s, "")
      case 1 => { val (name, label) = s span (_ != ':')
                  Node(name, label.tail) }
      case _ => throw new IllegalArgumentException(
        "too many ':' in node string")
    }


  // --- (Multi-)Edges ---

  /** Labelled directed multi-edge.
    *
    * @tparam N the type of nodes.
    * @param label label of the edge.
    */
  class EqDiEdge[N](nodes: Product, override val label: Label)
      extends DiEdge[N](nodes)
         with EdgeCopy[EqDiEdge]
         with OuterEdge[N,EqDiEdge] {

    override def copy[N](newNodes: Product) =
      new EqDiEdge[N](newNodes, label)
    
    override def equals(other: Any) = other match {
      case that: EqDiEdge[_] => this eq that
      case _ => false
    }

    override def hashCode: Int = {
      val h = System.identityHashCode(this)
      (h << 1) - (h << 8) // for optimized hash distribution
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

  object EqDiEdge {

    val nodeSeparator = "~+>"
    
    def apply(from: Node, to: Node, label: Label) =
      new EqDiEdge[Node](NodeProduct(from, to), label)
    
    def unapply(e: EqDiEdge[Node]) = Some(e)
    
    // def apply[N](from: N, to: N, label: Label) =
    //   new EqDiEdge[N](NodeProduct(from, to), label)
    
    // def unapply[N](e: EqDiEdge[N]) = Some(e)
  }
    
  // final implicit class NodeToEdge[N](n1: N) {
  //   def ~+>(n2: N)(label: Label) = new EqDiEdge[N]((n1, n2), label)
  // }

  final implicit class NodeToEdge(n1: Node) {
    def ~+>(n2: Node)(label: Label) =
      new EqDiEdge[Node]((n1, n2), label)
  }

  final implicit class StringToEdge(s1: String) {
    def ~+>(s2: String)(label: Label) =
      new EqDiEdge[Node]((strToNode(s1), strToNode(s2)), label)
  }

  object :~> {
    def unapply(e: EqDiEdge[Node]): Option[(Node, Node, Label)] =
      if (e eq null) None else Some((e._1, e._2, e.label))

    // def unapply[N](e: EqDiEdge[N]): Option[(N, N, Label)] =
    //   if (e eq null) None else Some((e._1, e._2, e.label))
  }

  object + {
    def unapply(nl: (Node, Label)): Option[(Node, Label)] =
      if (nl eq null) None else Some((nl._1, nl._2))

    // def unapply[N](nl: (N,Label)): Option[(N,Label)] =
    //   if (nl eq null) None else Some((nl._1, nl._2))
  }


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
        strToNode(n1.name + "," + n2.name + ":" + n1.label)
      val g = Graph[Node,EqDiEdge](nodesOut:_*)

      // Set-product injections
      val i1 = (nodesOut, g1nodes).zipped.toMap
      val i2 = (nodesOut, g2nodes).zipped.toMap

      // add edges
      val edges: Seq[(Edge, g1.EdgeT, g2.EdgeT)] =
        for {
          u <- nodesOut;
          v <- nodesOut;
          e1 <- i1(u) outgoingTo i1(v);
          e2 <- i2(u) outgoingTo i2(v);
          if e1 matches e2
        } yield ((u ~+> v)(e1.label), e1, e2)

      for (i <- 0 to edges.length;
           es <- edges.combinations(i)) yield {
        // put the new and old edges apart
        val (edgesOut, g1edges, g2edges) = es.unzip3
        // graph with edges
        val h: Graph = g ++ edgesOut
        // inner nodes and edges
        val nodesIn: Seq[h.NodeT] = nodesOut map h.get
        val edgesIn: Seq[h.EdgeT] =
          pair(edgesOut, h)(h.edges.to[ArrayBuffer]) map (_._2)
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

  /** Pair outer and inner edges in a given graph using `=~=`. */
  private def pair(edgesOut: Seq[Edge], g: Graph)(
    edgesIn: ArrayBuffer[g.EdgeT]): Seq[(Edge, g.EdgeT)] =
    edgesOut match {
      case Seq() => if (edgesIn.isEmpty) List()
                    else throw new IllegalArgumentException(
                      "unpaired edges in " + edgesIn)
      case e1 +: out => edgesIn find (_ =~= e1) match {
        case Some(e2) => (e1, e2) +: pair(out, g)(edgesIn - e2)
        case None => throw new IllegalArgumentException(
          "edge " + e1 + " doesn't pair with any edge in " + edgesIn)
      }
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
  def unions(g1: Graph, g2: Graph): Seq[Graph] = {
    val (pbs, m1, m2) = intersections(g1, g2).unzip3
    // get missing nodes
    val g1nodes = g1.nodes.toSeq
    val g2nodes = g2.nodes.toSeq
    // add missing nodes

    // get missing edges
    val g1edges = g1.edges.toSeq
    val g2edges = g2.edges.toSeq
    // add missing edges

    pbs
  }

  def relevantLeftUnions(g: Graph, r: Rule): Seq[Graph] = {
    List()
  }

  def relevantRightUnions(g: Graph, r: Rule): Seq[Graph] = {
    List()
  }


  // --- Fragmentation ---

  type Rate = Double
  type Prod = Seq[Graph]
  type Poly = Seq[(Rate, Prod)]
  type ODE = (Graph, Poly)

  def fragmentation(observables: Seq[Graph], rules: Seq[Rule],
    invariants: Graph => Graph = (x => x)): Seq[ODE] = {
    List()
  }


  // --- Arrows ---

  abstract class MonicPartial {

    val dom: Graph
    val cod: Graph

    val fn: Map[dom.NodeT, cod.NodeT]
    val fe: Map[dom.EdgeT, cod.EdgeT]

    /** Check if this arrow is monic. */
    def isValid: Boolean =
      fn.values.toSeq.combinations(2).forall { case Seq(n1, n2) => n1 != n2 } &&
      fe.values.toSeq.combinations(2).forall { case Seq(e1, e2) => e1 != e2 }

    def apply(u: dom.NodeT): cod.NodeT = fn(u)
    def apply(e: dom.EdgeT): cod.EdgeT = fe(e)

    def className: String = "MonicPartial"

    override def toString =
      className + "(" + (fn mkString ", ") +
      (if (fn.nonEmpty && fe.nonEmpty) ", " else "") +
      (fe mkString ", ") + ")"
  }

  object MonicPartial {
    def apply(from: Graph, to: Graph)(
      nodeMap: Map[from.NodeT, to.NodeT],
      edgeMap: Map[from.EdgeT, to.EdgeT]) = new MonicPartial {
      val dom = from
      val cod = to
      // val fn = (for ((n1,n2) <- nodeMap)
      //           yield (dom.get(n1),
      //                  cod.get(n2))).toMap
      // val fe = (for ((e1,e2) <- edgeMap)
      //           yield (dom.get(e1.toOuter),
      //                  cod.get(e2.toOuter))).toMap
      val fn = nodeMap.asInstanceOf[Map[dom.NodeT, cod.NodeT]]
      val fe = edgeMap.asInstanceOf[Map[dom.EdgeT, cod.EdgeT]]

      if (!isValid) throw new IllegalStateException(
        "given node or edge maps are not injective")
    }
  }


  abstract class MonicTotal extends MonicPartial {

    /** Check if this arrow is monic and total. */
    override def isValid: Boolean =
      super.isValid && 
      dom.nodes.forall(fn.isDefinedAt(_)) &&
      dom.edges.forall(fe.isDefinedAt(_))

    override def className: String = "Match"
  }

  object MonicTotal {
    def apply(from: Graph, to: Graph)(
      nodeMap: Map[from.NodeT, to.NodeT],
      edgeMap: Map[from.EdgeT, to.EdgeT]) = new MonicTotal {
      val dom = from
      val cod = to
      val fn = nodeMap.asInstanceOf[Map[dom.NodeT, cod.NodeT]]
      val fe = edgeMap.asInstanceOf[Map[dom.EdgeT, cod.EdgeT]]

      if (!isValid) throw new IllegalStateException(
        "given node or edge maps are not total or injective")
    }
  }


  type Match = MonicTotal
  val  Match = MonicTotal

  val observables: Seq[Graph] = List()
  val matches = Map[Graph, Seq[Match]]()


  // --- Actions ---

  sealed abstract class Action {
    def apply (m: Match): (Seq[m.cod.NodeT], Seq[m.cod.EdgeT])
  }

  case class AddNode(node: Node) extends Action {
    def apply(m: Match): (Seq[m.cod.NodeT], Seq[m.cod.EdgeT]) =
      (List(), List())
  }

  case class DelNode(node: Node) extends Action {
    def apply(m: Match): (Seq[m.cod.NodeT], Seq[m.cod.EdgeT]) =
      (List(), List())
  }

  case class AddEdge(edge: Edge) extends Action {
    def apply(m: Match): (Seq[m.cod.NodeT], Seq[m.cod.EdgeT]) =
      (List(), List())
  }

  case class DelEdge(edge: Edge) extends Action {
    def apply(m: Match): (Seq[m.cod.NodeT], Seq[m.cod.EdgeT]) =
      (List(), List())
  }

  // --- Rules ---

  class Rule(val lhs: Graph, val rhs: Graph, val rate: Rate)
      extends MonicPartial {

    val dom = lhs
    val cod = rhs
    val fn = (dom.nodes, cod.nodes).zipped.toMap
    val fe = (dom.edges, cod.edges).zipped.toMap

    val actions : Seq[Action] = List()

    /** Rewrites the codomain of `m` according to this rule.
      *
      * @return the collection of modified nodes and edges.
      */
    def rewrite(m: Match): (Seq[m.cod.NodeT], Seq[m.cod.EdgeT]) =
      collect(for (action <- actions) yield action(m))

    def collect[A,B](xys: Seq[(Seq[A], Seq[B])]): (Seq[A], Seq[B]) =
      xys.foldLeft((List[A](), List[B]())) {
        case ((xs, ys), (xss, yss)) => (xs ++ xss, ys ++ yss) }
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

