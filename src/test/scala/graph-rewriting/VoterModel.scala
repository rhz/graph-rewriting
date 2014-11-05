package graph_rewriting

import implicits._
import meanfield._

object VoterModel {
  def main(args: Array[String]): Unit = {
    val (e1, e2, e3) = ("u" ~~> "v", "u" ~~> "w", "v" ~~> "w")
    val rb = Graph("u" -> "red", "v" -> "blue")(e1)
    val bb = Graph("u" -> "blue", "v" -> "blue")(e1)
    val rr = Graph("u" -> "red", "v" -> "red")(e1)
    val rbw = rb + "w"
    val rwb = rbw + e2; rwb -= e1
    val bwr = rbw + e3; rwb -= e1

    // Flipping rules
    val b2r = Rule(rb, rr, 1)
    val r2b = Rule(rb, bb, 10)
    // TODO: missing rules where edge is blue to red

    // Flapping rules
    val flaprb = Rule(rbw, rwb, 100)
    val flapbr = Rule(rbw, bwr, 1000)
    // TODO: same missing rules here (see above)

    // For rewire-to-same rules, uncomment these lines
    // val r = Graph("w" -> "red")()
    // val b = Graph("w" -> "blue")()
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
    val r = Graph("u" -> "red")()

    // Transformers
    type NL = String
    type EL = String
    def paPn(g: Graph[N,NL,E,EL], n1: N, n2: N, n3: N) =
      Pn(Mn(g.inducedSubgraph(Set(n1, n2))) *
            g.inducedSubgraph(Set(n2, n3)) /
            g.inducedSubgraph(Set(n2))) // n2 is intersection
    // TODO: How can we make the splitting mechanism more generic?
    // Of course, paPn should have Set[N], Set[N] as parameters and
    // the intersection should be computed from these 2 sets.
    def pairApproximation(g: Graph[N,NL,E,EL])
        : Option[Pn[N,NL,E,EL]] =
      if (g.nodes.size == 3 && g.isConnected) {
        // extract the 3 nodes from the graph
        val Seq(n1, n2, n3) = g.nodes.toSeq
        // get n1's neighbours that aren't itself
        val nbs = g(n1).neighbours - n1
        // if it has only one neighbour it must be on the side
        // of the chain (assuming it's not a triangle)
        if (nbs.size == 1) {
          // if that neighbour is n2, then that's the intersection
          if (nbs contains n2) Some(paPn(g, n1, n2, n3))
          // otherwise n3 must be the intersection
          else Some(paPn(g, n1, n3, n2))
          // if n1 has two neighbours, then n1 is the intersection
        } else Some(paPn(g, n2, n1, n3))
        // NOTE: the triangle case is not handled by this function
        // and in case one is given, it will destroy the edge between
        // n2 and n3
      } else None

    // Fragmentation
    val eqs = mfa(List(r2b, b2r), List(r), pairApproximation _)
    eqs.printEqs
  }
}

