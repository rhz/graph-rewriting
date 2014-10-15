package graph_rewriting


case class Rule[N,NL,E<:DiEdgeLike[N],EL](
  val lhs: Graph[N,NL,E,EL],
  val rhs: Graph[N,NL,E,EL],
  fn: Map[N,N], fe: Map[E,E]) extends PInj[N,E,N,E](fn, fe) {

  var rate: Double = 1.0

  type Match = PInj[N,E,N,E]

  def apply(m: Match): (Match, Seq[N], Seq[E]) = ???

  def reversed = Rule[N,NL,E,EL](rhs, lhs,
    n map (_.swap), e map (_.swap))
}


/*
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

    type Rate = Double

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
*/

