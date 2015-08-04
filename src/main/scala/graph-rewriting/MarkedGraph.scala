package uk.ac.ed.inf
package graph_rewriting

// This is needed because mutable.Map.keySet returns a collection.Set
// and thus Node.edges has to be of this type.  Then the line
// adjacency(n)(e) = (e.nodes - n) forces adjacency to be of type
// mutable.Map[N, mutable.Map[E, collection.Set[N]]] and so it
// propagates everywhere.
import scala.collection.Set
import scala.collection.mutable

import scala.language.higherKinds  // TODO: necessary?

import utils._

abstract class BaseMarkedDiGraph[N,NL,E<:DiEdgeLike[N],EL]
    extends BaseDiGraph[N,NL,E,EL] {

  // type G[Y,Z<:E,W] <: BaseMarkedDiGraph[N,Y,Z,W]
  override def stringPrefix = "MarkedDiGraph"

  // FIXME: This is a hack to work around the issue with type G that can't
  // be given an upper bound here or it won't mix with ConcreteDiGraph
  override def copy =
    super.copy match {
      case g: BaseMarkedDiGraph[N,NL,E,EL] => {
        for (n <- inMarks) g(n).inMark
        for (n <- outMarks) g(n).outMark
        g.asInstanceOf[This] // since copy returned a BaseMarkedDiGraph, this is safe
      }
      case g => g
    }

  val inMarks = mutable.Set.empty[N]
  val outMarks = mutable.Set.empty[N]

  class MarkedNode(n: N) extends DiNode(n) {
    def marked: Boolean = (inMarks contains n) || (outMarks contains n)
    def inMarked: Boolean = inMarks contains n
    def outMarked: Boolean = outMarks contains n
    def mark = { inMarks += n; outMarks += n; this }
    def unmark = { inMarks -= n; outMarks -= n; this }
    def inMark = { inMarks += n; this }
    def inUnmark = { inMarks -= n; this }
    def outMark = { outMarks += n; this }
    def outUnmark = { outMarks -= n; this }
  }

  override def apply(n: N): MarkedNode =
    if (nodes contains n) new MarkedNode(n)
    else throw new NoSuchElementException(
      "no such node " + n + " in graph " + this)

  def mark(n: N, ns: N*): this.type = {
    require(nodes contains n, s"node $n not in graph $this")
    inMarks += n; outMarks += n
    for (n <- ns) {
      require(nodes contains n, s"node $n not in graph $this")
      inMarks += n; outMarks += n
    }
    this
  }
  def mark(ns: Traversable[N]): this.type = {
    for (n <- ns) {
      require(nodes contains n, s"node $n not in graph $this")
      inMarks += n; outMarks += n
    }
    this
  }
  def inMark(n: N, ns: N*): this.type = {
    require(nodes contains n, s"node $n not in graph $this")
    inMarks += n
    for (n <- ns) {
      require(nodes contains n, s"node $n not in graph $this")
      inMarks += n
    }
    this
  }
  def inMark(ns: Traversable[N]): this.type = {
    for (n <- ns) {
      require(nodes contains n, s"node $n not in graph $this")
      inMarks += n
    }
    this
  }
  def outMark(n: N, ns: N*): this.type = {
    require(nodes contains n, s"node $n not in graph $this")
    outMarks += n
    for (n <- ns) {
      require(nodes contains n, s"node $n not in graph $this")
      outMarks += n
    }
    this
  }
  def outMark(ns: Traversable[N]): this.type = {
    for (n <- ns) {
      require(nodes contains n, s"node $n not in graph $this")
      outMarks += n
    }
    this
  }

  // We might want to override this method and addEdges
  // to disallow the creation of edges at marked nodes.
  // override def += (e: E): this.type = ???

  override def -= (n: N): this.type = {
    super.-=(n)
    if (inMarks contains n) inMarks -= n
    if (outMarks contains n) outMarks -= n
    this
  }

  // NOTE: This doesn't work because in graph with internal symmetries
  // there will be more than one bijection and maybe the chosen one
  // doesn't map the marks correctly.
  // override def connectedIso(that: BaseDiGraph[N,NL,E,EL]): Boolean =
  //   that match {
  //     case thatM: BaseMarkedDiGraph[_,_,_,_] =>
  //       (this eq that) ||
  //       ((this.nodes.size == that.nodes.size) &&
  //        (this.edges.size == that.edges.size) && {
  //          val f = findBijection(that)
  //          f.isDefined && (
  //            (inMarks map f.get.n) == thatM.inMarks) && (
  //            (outMarks map f.get.n) == thatM.outMarks)
  //        })
  //     case _ => super.connectedIso(that)
  //   }

  // TODO: Lot of code duplication here, this long function is
  // essentially the same as DiGraph.findBijection.
  override def findBijection[N2,E2<:DiEdgeLike[N2],
    H[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    that: H[N2,NL,E2,EL])(implicit ev: This <:< H[N,NL,E,EL])
      : Option[Arrow[N,NL,E,EL,N2,NL,E2,EL,H]] = that match {

    case thatM: BaseMarkedDiGraph[_,_,_,_] => {

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
        if (queue.isEmpty) Some(Arrow(this.asThis,thatM.asInstanceOf[H[N2,NL,E2,EL]],fn,fe))
        else {
          val (u,v) = queue.head
          if ((this(u).inDegree != thatM(v).inDegree) ||
              (this(u).outDegree != thatM(v).outDegree) ||
              (this(u).inMarked != thatM(v).inMarked) ||
              (this(u).outMarked != thatM(v).outMarked)) None
          else {
            // TODO: I should probably carry not just the edges here
            // but also the neighbours
            val uin = this(u).incoming.toVector groupBy (this(_).label)
            val uout = this(u).outgoing.toVector groupBy (this(_).label)
            val vin = thatM(v).incoming.toVector groupBy (thatM(_).label)
            val vout = thatM(v).outgoing.toVector groupBy (thatM(_).label)

            // if the nodes have the same degree and the sets of labels
            // are equal then there's a posibility that u matches v
            if ((uin.keySet != vin.keySet) ||
                (uout.keySet != vout.keySet) ||
                (uin exists { case (label,edges) =>
                  edges.size != vin(label).size }) ||
                (uout exists { case (label,edges) =>
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
                  un = this(u).opp(ue)
                  vn = thatM(v).opp(ve)
                  if this(un) matches thatM(vn)
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
                  val nbs = (indices,edges).zipped map ((i,xs) => xs(i))
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
                    result = extendBijection(q,mfn,mfe,mns,mes)
                  if (updateIndices)
                    finished = true
                }
                result
              }
            }
          }
        }

      if (this.nodes.size == 1 && thatM.nodes.size == 1) {
        if ((this(this.nodes.head).label == thatM(thatM.nodes.head).label) &&
            (this(this.nodes.head).inMarked == thatM(thatM.nodes.head).inMarked) &&
            (this(this.nodes.head).outMarked == thatM(thatM.nodes.head).outMarked))
          // FIXME: What if `{this,thatM}.nodes.head` has self-loops?
          Some(Arrow[N,NL,E,EL,N2,NL,E2,EL,H](this.asThis,
            thatM.asInstanceOf[H[N2,NL,E2,EL]],
            Map(this.nodes.head -> thatM.nodes.head),Map.empty[E,E2]))
        else None
      } else {
        // map node labels to nodes
        val domNodesByLabel = this.nodes groupBy (this(_).label)
        val codNodesByLabel = thatM.nodes groupBy (thatM(_).label)

        // the distribution of labels must be the same
        if ((domNodesByLabel.keySet != codNodesByLabel.keySet) ||
          (domNodesByLabel exists { case (l,ns) =>
            ns.size != codNodesByLabel(l).size })) None
        else {
          // look for the least populated label in the codomain
          val (label,codNodes) = codNodesByLabel minBy (_._2.size)

          // get an anchor in the domain for that label
          val anchor = domNodesByLabel(label).head

          codNodes.collectFirst(Function.unlift { c: N2 =>
            extendBijection(Vector(anchor -> c), Map(anchor -> c),
              Map.empty, Set.empty, Set.empty) })
        }
      }
    }
    case _ => super.findBijection(that)
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
        // TODO: Why doesn't the type inference work here?
        (pb,f1,f2) <- super.intersections[N2,E2,N3,E3,H](that)
        pbM = pb.asInstanceOf[BaseMarkedDiGraph[N3,NL,E3,EL]] // since H <: BaseMarkedDiGraph this should just be an upcast
        if (pbM.nodes forall (n =>
          (this(f1(n)).inMarked, thatM(f2(n)).inMarked) match {
            case (false,false) => true
            case (true,true) => {
              // pbM(n).inMark // add mark
              val d = pbM(n).inDegree
              (d <= this(f1(n)).inDegree) && (d <= thatM(f2(n)).inDegree)
            }
            case (true,false) => {
              // pbM(n).inMark // add mark
              val d = pbM(n).inDegree
              (d <= this(f1(n)).inDegree)
            }
            case (false,true) => {
              // pbM(n).inMark // add mark
              val d = pbM(n).inDegree
              (d <= thatM(f2(n)).inDegree)
            }
          }))
        if (pbM.nodes forall (n =>
          (this(f1(n)).outMarked, thatM(f2(n)).outMarked) match {
            case (false,false) => true
            case (true,true) => {
              // pbM(n).outMark // add mark
              val d = pbM(n).outDegree
              (d <= this(f1(n)).outDegree) && (d <= thatM(f2(n)).outDegree)
            }
            case (true,false) => {
              // pbM(n).outMark // add mark
              val d = pbM(n).outDegree
              (d <= this(f1(n)).outDegree)
            }
            case (false,true) => {
              // pbM(n).outMark // add mark
              val d = pbM(n).outDegree
              (d <= thatM(f2(n)).outDegree)
            }
          }))
        pbH = pbM.asInstanceOf[H[N3,NL,E3,EL]] // and here we downcast pb back to what it actually is
      } yield (pbH, Arrow[N3,NL,E3,EL,N ,NL,E ,EL,H](pbH,this.asThis,f1.n,f1.e),
                    Arrow[N3,NL,E3,EL,N2,NL,E2,EL,H](pbH,that,f2.n,f2.e))
    case _ => super.intersections(that)
  }

  override def intersectionsAndUnions[
    N2,E2<:DiEdgeLike[N2],N3,E3<:DiEdgeLike[N3],
    H[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    that: H[N2,NL,E2,EL])(implicit
      nodeUnifier: Unifier[N,N2,N3],
      edgeUnifier: (H[N3,NL,E3,EL],Map[N,N3],Map[N2,N3]) => Unifier[E,E2,E3],
      graphBuilder: () => H[N3,NL,E3,EL],
      ev: This <:< H[N,NL,E,EL])
      : Seq[(H[N3,NL,E3,EL],
             Arrow[N3,NL,E3,EL,N ,NL,E ,EL,H],
             Arrow[N3,NL,E3,EL,N2,NL,E2,EL,H],
             H[N3,NL,E3,EL],
             Arrow[N ,NL,E ,EL,N3,NL,E3,EL,H],
             Arrow[N2,NL,E2,EL,N3,NL,E3,EL,H])] = that match {
    case thatM: BaseMarkedDiGraph[N2,NL,E2,EL] => // H <: BaseMarkedDiGraph
      for {
        (pb,g1,g2,po,f1,f2) <- super.intersectionsAndUnions[N2,E2,N3,E3,H](that)
        poM = po.asInstanceOf[BaseMarkedDiGraph[N3,NL,E3,EL]] // since H <: BaseMarkedDiGraph this should just be an upcast
        f1i = f1.n.inverse
        f2i = f2.n.inverse
        if (poM.nodes forall (n =>
          (f1i get n, f2i get n) match {
            case (Some(u),None) => {
              if (this(u).inMarked)
                poM(n).inMark // add mark
              if (this(u).outMarked)
                poM(n).outMark // add mark
              true // since `n` is not in the intersection
              // it will never have a degree different to `u`
            }
            case (None,Some(v)) => {
              if (thatM(v).inMarked)
                poM(n).inMark // add mark
              if (thatM(v).outMarked)
                poM(n).outMark // add mark
              true // since `n` is not in the intersection
              // it will never have a degree different to `v`
            }
            case (Some(u),Some(v)) => {
              if (this(u).inMarked || thatM(v).inMarked)
                poM(n).inMark // add mark
              if (this(u).outMarked || thatM(v).outMarked)
                poM(n).outMark // add mark
              (!this(u).inMarked || (poM(n).inDegree == this(u).inDegree)) &&
              (!thatM(v).inMarked || (poM(n).inDegree == thatM(v).inDegree)) &&
              (!this(u).outMarked || (poM(n).outDegree == this(u).outDegree)) &&
              (!thatM(v).outMarked || (poM(n).outDegree == thatM(v).outDegree))
            }
            case (None,None) => throw new IllegalStateException(
              s"node $n in union $po doesn't have a pre-image " +
              s"in arguments $this or $that.")
          }))
        poH = poM.asInstanceOf[H[N3,NL,E3,EL]] // and here we downcast pb back to what it actually is
      } yield (pb,g1,g2,poH,
        Arrow[N ,NL,E ,EL,N3,NL,E3,EL,H](this.asThis,poH,f1.n,f1.e),
        Arrow[N2,NL,E2,EL,N3,NL,E3,EL,H](that,poH,f2.n,f2.e))
    case _ => super.intersectionsAndUnions(that)
  }

  override def rightUnions[
    H[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    r: Rule[N,NL,E,EL,H])(implicit
      nodeUnifier: Unifier[N,N,N],
      edgeUnifier: (H[N,NL,E,EL],Map[N,N],Map[N,N]) => Unifier[E,E,E],
      graphBuilder: () => H[N,NL,E,EL],
      ev: This <:< H[N,NL,E,EL])
      : Seq[H[N,NL,E,EL]] =
    // TODO: The strongest post-condition RHS should be constructed here
    // since we only use it to discard non-derivable matches,
    // but how do we do that in an efficient way?
    for ((mg,_,m) <- unions[N,E,N,E,H](r.rhs);
      _ = r.reversed()(m)) yield mg

  def nodeToString[M](u: N, v: M) =
    (inMarks contains u, outMarks contains u) match {
      case (true,true)  => "|" + v + "|"
      case (true,false) => ">" + v + "<"
      case (false,true) => "<" + v + ">"
      case (false,false) => v
    }

  override def toString = s"$stringPrefix(nodes = " +
    nodes.map(n => nodeToString(n,n)) + s", edges = $edges" +
    (if (nodelabels.nonEmpty) s", nodelabels = $nodelabels" else "") +
    (if (edgelabels.nonEmpty) s", edgelabels = $edgelabels" else "") + ")"

  override def toString[M](nm: Map[N,M]) = {
    val em = (for (e <- edges) yield
      (e, e.copy(nm(e.source), nm(e.target)))).toMap
    val nl = for ((n,l) <- nodelabels) yield (nm(n),l)
    val el = for ((e,l) <- edgelabels) yield (em(e),l)
    s"$stringPrefix(nodes = Set(" + nm.map({ case (u,v) =>
      nodeToString(u,v) }).mkString(", ") + "), " +
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

  class MarkedDiGraphConstructor[N,NL,E<:DiEdgeLike[N],EL] {
    def apply(nodes: (N,Option[NL])*)(edges: (E,Option[EL])*)
        : MarkedDiGraph[N,NL,E,EL] = const(nodes,edges)
    def apply(nodes: Iterable[N], edges: Iterable[E])
        : MarkedDiGraph[N,NL,E,EL] =
      const[N,NL,E,EL](nodes zip Stream.continually(None),
                       edges zip Stream.continually(None))
    def empty: MarkedDiGraph[N,NL,E,EL] = new MarkedDiGraph[N,NL,E,EL]
  }

  def withType[N,NL,E<:DiEdgeLike[N],EL] =
    new MarkedDiGraphConstructor[N,NL,E,EL]
}

