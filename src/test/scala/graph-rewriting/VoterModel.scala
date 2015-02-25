package graph_rewriting

import implicits._
import meanfield._

object VoterModel {
  type NL = String
  type EL = String
  val G = Graph.withType[N,NL,E,EL]
  def main(args: Array[String]): Unit = {
    val (e1, e2, e3) = ("u" ~~> "v", "u" ~~> "w", "v" ~~> "w")
    val rb = G("u" -> "red", "v" -> "blue")(e1)
    val bb = G("u" -> "blue", "v" -> "blue")(e1)
    val rr = G("u" -> "red", "v" -> "red")(e1)
    val rbw = rb + "w"
    val rwb = rbw + e2; rwb -= e1
    val bwr = rbw + e3; rwb -= e1

    // Flipping rules
    val b2r = Rule(rb, rr, "Ibr")
    val r2b = Rule(rb, bb, "Irb")
    // TODO: missing rules where edge is blue to red

    // Flapping rules
    val flapbr = Rule(rbw, bwr, "Abr")
    val flaprb = Rule(rbw, rwb, "Arb")
    // TODO: same missing rules here (see above)

    // For rewire-to-same rules, uncomment these lines
    // val r = G("w" -> "red")()
    // val b = G("w" -> "blue")()
    // val rrb = rb + r; rrb += e2 -= e1
    // val rbb = rb + b; rbb += e3 -= e1
    // val flaprb = Rule(rb + r, rrb, 100)
    // val flapbr = Rule(rb + r, rbb, 1000)

    // For rewire-to-foaf, uncomment the following
    // val rbf = rbw + e3
    // val rfb = rbf + e2; rfb -= e1
    // val frb = rbw + e2
    // val bfr = frb + e3; bfr -= e1
    // val flaprb = Rule(rbf, rfb, 100)
    // val flapbr = Rule(frb, bfr, 1000)

    // Observables
    val r = G("u" -> "red")()

    // Transformers
    def paMn(g: Graph[N,NL,E,EL], n1: N, n2: N, n3: N) =
      Mn(g.inducedSubgraph(Set(n1, n2))) *
         g.inducedSubgraph(Set(n2, n3)) /
         g.inducedSubgraph(Set(n2)) // n2 is intersection

    // TODO: How can we make the splitting mechanism more generic?
    // Of course, paPn should have Set[N], Set[N] as parameters and
    // the intersection should be computed from these 2 sets, but the
    // hard part is how to split g.nodes into these 2 sets.
    def pairApproximation(g: Graph[N,NL,E,EL])
        : Option[Mn[N,NL,E,EL]] =
      if (g.nodes.size == 3 && g.isConnected) {
        // extract the 3 nodes from the graph
        val Seq(n1, n2, n3) = g.nodes.toSeq
        // get n1's neighbours that aren't itself
        val nbs = g(n1).neighbours - n1
        // if it has only one neighbour it must be on the side
        // of the chain (assuming it's not a triangle)
        if (nbs.size == 1) {
          // if that neighbour is n2, then that's the intersection
          if (nbs contains n2) Some(paMn(g, n1, n2, n3))
          // otherwise n3 must be the intersection
          else Some(paMn(g, n1, n3, n2))
          // if n1 has two neighbours, then n1 is the intersection
        } else Some(paMn(g, n2, n1, n3))
        // NOTE: the triangle case is not handled by this function
        // and in case one is given, it will destroy the edge between
        // n2 and n3
      } else None

    def destroyParallelEdges(g: Graph[N,NL,E,EL])
        : Option[Mn[N,NL,E,EL]] = {
      val h = g.copy
      var parallelEdges = false
      for {
        u <- h.nodes
        v <- h.nodes
        u2v = h(u).edgesTo(v)
        if u2v.size > 1
      } {
        parallelEdges = true
        // we assume that all edges from u to v have the same label
        assume(u2v.toSeq.sliding(2) forall {
          case Seq(e1, e2) => h(e1).label == h(e2).label
        }, s"edges from $u to $v do not have the same label, " +
            "can't merge them.")
        h.delEdges(u2v.tail)
      }
      if (parallelEdges) Some(Mn(h))
      else None
    }

    // Fragmentation
    val eqs = mfa(List(r2b, b2r, flaprb, flapbr), List(r),
      splitConnectedComponents[N,NL,E,EL] _,
      pairApproximation _,
      destroyParallelEdges _)
    ODEPrinter(eqs).print
  }
}

