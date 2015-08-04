package uk.ac.ed.inf
package graph_rewriting

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
 * The abstract base class of directed graphs (digraphs).
 *
 * @tparam N the type of nodes in this graph
 * @tparam NL the type of node labels in this graph
 * @tparam E the type of edges in this graph
 * @tparam EL the type of edge labels in this graph
 */
abstract class BaseDiGraph[N, NL, E <: DiEdgeLike[N], EL]
    extends BaseGraph[N, NL, E, EL] {

  override def stringPrefix = "DiGraph"

  type This <: BaseDiGraph[N, NL, E, EL]

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
  def arrowsTo[N2,E2<:DiEdgeLike[N2],
    H[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    that: H[N2,NL,E2,EL])(implicit ev: This <:< H[N,NL,E,EL])
      : Vector[Arrow[N,NL,E,EL,N2,NL,E2,EL,H]] = {

    /** Tries to construct a total `Arrow` from a partial one.
      *
      * @param queue nodes that should be visited next, in order.
      * @param nodeMap partial injection on nodes that we are extending.
      * @param edgeMap partial injection on edges that we are extending.
      * @param seenNodes nodes seen in the image of the injection.
      * @param seenEdges nodes seen in the image of the injection.
      */
    def extendArrow(queue: Seq[(N,N2)], fn: Map[N,N2], fe: Map[E,E2],
      ns: Set[N2], es: Set[E2]): Vector[Arrow[N,NL,E,EL,N2,NL,E2,EL,H]] =
      // If there's nothing else to visit, we stop and return the injection we found
      if (queue.isEmpty) Vector(Arrow(this.asThis,that,fn,fe))
      else {
        val (u,v) = queue.head
        val (uout,uin) = this.adjacency(u).toVector.partition({
          case (e,ns) => e.source == u })
        val (vout,vin) = that.adjacency(v).toVector.partition({
          case (e,ns) => e.source == v })
        // println(s"u = $u, v = $v")

        // val uin = adjacency(u).toVector groupBy (this(_._1).label)
        // val uout = adjacency(u).toVector groupBy (this(_._1).label)
        // val uin = this(u).incoming.toVector groupBy (this(_).label)
        // val uout = this(u).outgoing.toVector groupBy (this(_).label)
        // val vin = that(v).incoming.toVector groupBy (that(_).label)
        // val vout = that(v).outgoing.toVector groupBy (that(_).label)

        if ((uout.size > vout.size) || (uin.size > vin.size)) Vector()
        else {

          val uinByLabel = uin groupBy { case (e,_) => this(e).label }
          val vinByLabel = vin groupBy { case (e,_) => that(e).label }
          val uoutByLabel = uout groupBy { case (e,_) => this(e).label }
          val voutByLabel = vout groupBy { case (e,_) => that(e).label }

          // if the nodes have the same degree and the sets of labels
          // are equal then there's a posibility that u matches v
          if (uinByLabel.exists({ case (label,edges) =>
                !vinByLabel.contains(label) ||
                (edges.size > vinByLabel(label).size) }) &&
              uoutByLabel.exists({ case (label,edges) =>
                !voutByLabel.contains(label) ||
                (edges.size > voutByLabel(label).size) })) Vector()
          else {
            // sort incoming and outgoing edges by the number of
            // combinations that we have to try to reject
            val uinSorted = uinByLabel.toVector.sortBy(_._2.size)
            val uoutSorted = uoutByLabel.toVector.sortBy(_._2.size)

            def matchingEdges(xs: Vector[(Option[EL],Vector[(E,Set[N])])],
              m: Map[Option[EL],Vector[(E2,Set[N2])]])
                : Vector[Vector[(E,N,E2,N2)]] =
              for ((label,edges) <- xs; (ue,uns) <- edges)
              yield (for {
                (ve,vns) <- m(label)
                un = uns.head
                vn = vns.head
                if this(un) matches that(vn)
                // Q: Should I return `uns` and `vns` in the result
                //    instead of `un` and `vn`?
              } yield (ue,un,ve,vn))

            // collect edges around u and v that match
            val edges = matchingEdges(uinSorted,vinByLabel) ++
                        matchingEdges(uoutSorted,voutByLabel)
            // println(s"edges = $edges")

            // if one of the edges doesn't have a match, then we stop
            if (edges exists (_.isEmpty)) Vector()
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
              type A = Arrow[N,NL,E,EL,N2,NL,E2,EL,H]
              var arrows: mutable.Builder[A,Vector[A]] = Vector.newBuilder
              while (!finished) {
                val nbs = (indices,edges).zipped map ((i,xs) => xs(i))
                var mfn = fn
                var mfe = fe
                var mes = es
                var mns = ns
                var q = queue.tail
                var failed = false
                for ((ue,un,ve,vn) <- nbs if failed == false) {
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
                  arrows ++= extendArrow(q,mfn,mfe,mns,mes)
                if (updateIndices)
                  finished = true
              }
              arrows.result
            }
          }
        }
      }

    if (this.nodes.size == 1 && that.nodes.size == 1) {
      if (this(this.nodes.head).label == that(that.nodes.head).label)
        // FIXME: What if `{this,that}.nodes.head` has self-loops?
        Vector(Arrow(this.asThis,that,
          Map(this.nodes.head -> that.nodes.head),Map.empty[E,E2]))
      else Vector()
    } else {
      // map node labels to nodes
      val domNodesByLabel = this.nodes groupBy (this(_).label)
      val codNodesByLabel = that.nodes groupBy (that(_).label)

      // the distribution of labels must be the same
      if (domNodesByLabel exists { case (label,nodes) =>
            !codNodesByLabel.contains(label) ||
            (nodes.size > codNodesByLabel(label).size) }) Vector()
      else {
        // look for the least populated label in the codomain
        val (label,codNodes) = codNodesByLabel minBy (_._2.size)

        // get an anchor in the domain for that label
        val anchor = domNodesByLabel(label).head

        codNodes.toVector flatMap { c: N2 =>
          extendArrow(Vector(anchor -> c), Map(anchor -> c),
            Map.empty, Set.empty, Set.empty) }
      }
    }
  }


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
                vn = that(v).opp(ve)
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

        codNodes.collectFirst(Function.unlift { c: N2 =>
          extendBijection(Vector(anchor -> c), Map(anchor -> c),
            Map.empty, Set.empty, Set.empty) })
      }
    }
  }


  // --- Intersections and Unions ---

  /** Intersections of subobjects of `this` and `that` graph.
    *
    * @return the set of graph intersections with their respective
    *         product injections.
    */
  def intersections[N2,E2<:DiEdgeLike[N2],N3,E3<:DiEdgeLike[N3],
    H[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    that: H[N2,NL,E2,EL])(implicit
      nodeUnifier: Unifier[N,N2,N3],
      edgeUnifier: (H[N3,NL,E3,EL],Map[N,N3],Map[N2,N3]) => Unifier[E,E2,E3],
      graphBuilder: () => H[N3,NL,E3,EL],
      ev: This <:< H[N,NL,E,EL])
      : Seq[(H[N3,NL,E3,EL],
             Arrow[N3,NL,E3,EL,N ,NL,E ,EL,H],
             Arrow[N3,NL,E3,EL,N2,NL,E2,EL,H])] = {

    val g1nodes: Seq[N] = this.nodes.toSeq
    val g2nodes: Seq[N2] = that.nodes.toSeq

    // set of nodes in `that` indexed by nodes in `this` that match
    val nodeMatches: Map[N,Seq[N2]] =
      (g1nodes, g1nodes map (u => g2nodes filter (v => {
        val n = this(u); val m = that(v);
        !n.isLabelled || !m.isLabelled || (n.label == m.label)
      }))).zipped.toMap

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
      val eu = edgeUnifier(g,fn1.inverse,fn2.inverse)
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
        } yield (eu.unify(e1,e2),e1,e2)

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

  def unions[N2,E2<:DiEdgeLike[N2],N3,E3<:DiEdgeLike[N3],
    H[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    that: H[N2,NL,E2,EL])(implicit
      nodeUnifier: Unifier[N,N2,N3],
      edgeUnifier: (H[N3,NL,E3,EL],Map[N,N3],Map[N2,N3]) => Unifier[E,E2,E3],
      graphBuilder: () => H[N3,NL,E3,EL],
      ev: This <:< H[N,NL,E,EL])
      : Seq[(H[N3,NL,E3,EL],
             Arrow[N ,NL,E ,EL,N3,NL,E3,EL,H],
             Arrow[N2,NL,E2,EL,N3,NL,E3,EL,H])] =
    for ((_,_,_,po,f1,f2) <- intersectionsAndUnions[N2,E2,N3,E3,H](that))
    yield (po,f1,f2)

  /** Unions of subobjects of `this` and `that`. */
  def intersectionsAndUnions[
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
             Arrow[N2,NL,E2,EL,N3,NL,E3,EL,H])] = {

    // This for shows that intersections and unions are in bijection
    for ((pb,f1,f2) <- intersections[N2,E2,N3,E3,H](that)) yield {
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
      val eu = edgeUnifier(pb,fn1,fn2)
      val e1s = for (e1 <- g1edges) yield eu.left(e1)
      val e2s = for (e2 <- g2edges) yield eu.right(e2)
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

      (pb,f1,f2,po,
        // TODO: Why aren't these types inferred?
        Arrow[N ,NL,E ,EL,N3,NL,E3,EL,H](this.asThis,po,fn1,fe1),
        Arrow[N2,NL,E2,EL,N3,NL,E3,EL,H](that,po,fn2,fe2))
    }
  }

  def leftUnions[
    H[X, Y, Z <: DiEdgeLike[X], W] <: BaseDiGraph[X, Y, Z, W]](
    r: Rule[N, NL, E, EL, H])(implicit
      nodeUnifier: Unifier[N, N, N],
      edgeUnifier: (H[N, NL, E, EL], Map[N, N], Map[N, N]) => Unifier[E, E, E],
      graphBuilder: () => H[N, NL, E, EL],
      ev: This <:< H[N, NL, E, EL])
      : Seq[H[N, NL, E, EL]] =
    // TODO: relevance test
    for ((mg, _, _) <- unions[N, E, N, E, H](r.lhs)) yield mg

  def rightUnions[
    H[X, Y, Z <: DiEdgeLike[X], W] <: BaseDiGraph[X, Y, Z, W] {
      type This = H[X, Y, Z, W]
    }](r: Rule[N, NL, E, EL, H])(implicit
      nodeUnifier: Unifier[N,N,N],
      edgeUnifier: (H[N, NL, E, EL], Map[N, N],Map[N, N]) => Unifier[E, E, E],
      graphBuilder: () => H[N, NL, E, EL],
      ev: This <:< H[N, NL, E, EL])
      : Seq[H[N, NL, E, EL]] = {
    val ropp = r.reversed
    for {
      (mg, _, m) <- unions[N, E, N, E, H](ropp.lhs)
      rmg = mg.copy; (comatch, _, _) = ropp(m)
      lmg = mg.copy; _ = r(comatch)
      // TODO: relevance test
      // derivability test
      if mg iso rmg
    } yield lmg
  }

  def toString[M](nm: Map[N,M]) = {
    val em = (for (e <- edges) yield
      (e, e.copy(nm(e.source), nm(e.target)))).toMap
    val nl = for ((n,l) <- nodelabels) yield (nm(n),l)
    val el = for ((e,l) <- edgelabels) yield (em(e),l)
    s"$stringPrefix(" +
      "nodes = Set(" + nm.values.mkString(", ") + "), " +
      "edges = Set(" + em.values.mkString(", ") + ")" +
      (if (nl.nonEmpty) s", nodelabels = $nl" else "") +
      (if (el.nonEmpty) s", edgelabels = $el" else "") + ")"
  }

  // TODO: toDot
  // override def toDot: String
}

/**
 * Directed graphs (digraphs).
 *
 * @tparam N the type of nodes in this graph
 * @tparam NL the type of node labels in this graph
 * @tparam E the type of edges in this graph
 * @tparam EL the type of edge labels in this graph
 */
class DiGraph[N, NL, E <: DiEdgeLike[N], EL]
    extends BaseDiGraph[N, NL, E, EL] {
  type This = DiGraph[N, NL, E, EL]
  def empty = new DiGraph[N,NL,E,EL]
  def asThis = this
}

// -- Node and Edge Unifiers (for intersections and unions) --

trait Unifier[T,U,V] {
  def unify(x: T, y: U): V
  def left(x: T): V
  def right(y: U): V
}

object DiGraph {

  // --- Constructors ---

  def apply[N,NL,E<:DiEdgeLike[N],EL](
    nodes: Traversable[(N,Option[NL])],
    edges: Traversable[(E,Option[EL])]): DiGraph[N,NL,E,EL] = {
    val g = new DiGraph[N,NL,E,EL]
    g.addNodes(nodes map (_._1))
    g.addEdges(edges map (_._1))
    for ((n, Some(l)) <- nodes) g(n).label = l
    for ((e, Some(l)) <- edges) g(e).label = l
    g
  }

  implicit def empty[N,NL,E<:DiEdgeLike[N],EL]() = new DiGraph[N,NL,E,EL]

  class DiGraphConstructorWithNodes[N,NL](
    nodes: Traversable[(N,Option[NL])]) {
    def apply[E<:DiEdgeLike[N],EL](edges: (E,Option[EL])*) =
      DiGraph(nodes, edges)
    def apply() = DiGraph[N,NL,IdDiEdge[Int,N],String](nodes, List())
  }

  def apply[N,NL](n1: (N,Option[NL]), nodes: (N,Option[NL])*) =
    new DiGraphConstructorWithNodes[N,NL](n1 +: nodes)

  class DiGraphConstructor[N, NL, E <: DiEdgeLike[N], EL] {
    def apply(nodes: (N, Option[NL])*)(edges: (E,Option[EL])*)
        : DiGraph[N, NL, E, EL] = DiGraph(nodes,edges)
    def apply(nodes: Iterable[N], edges: Iterable[E])
        : DiGraph[N, NL, E, EL] =
      DiGraph[N, NL, E, EL](
        nodes zip Stream.continually(None),
        edges zip Stream.continually(None))
    def empty: DiGraph[N, NL, E, EL] = new DiGraph[N, NL, E, EL]
  }

  def withType[N, NL, E <: DiEdgeLike[N], EL] =
    new DiGraphConstructor[N, NL, E, EL]


  // -- Isomorphisms of multiple directed graphs --

  // Q: Is the companion object really a good place to put this function?
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
