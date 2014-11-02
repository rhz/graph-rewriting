package graph_rewriting

import org.scalatest.{FlatSpec, Matchers}
import implicits._

class Bimotor extends FlatSpec with Matchers {

  "A bimotor" should "walk on DNA" in {
    val bc0 = "b" ~~> "c1"
    val bc1 = "b" ~~> "c1"
    val bc2 = "b" ~~> "c2"
    val bc3 = "b" ~~> "c2"
    val c1c2 = "c1" ~~> "c2"
    val g1 = Graph("b" -> "bimotor", "c1" -> "chain", "c2" -> "chain")(
      bc0, bc1, c1c2)
    val g2 = Graph("b" -> "bimotor", "c1" -> "chain", "c2" -> "chain")(
      bc1, bc2, c1c2)
    val g3 = Graph("b" -> "bimotor", "c1" -> "chain", "c2" -> "chain")(
      bc2, bc3, c1c2)
    val g4 = Graph("b" -> "bimotor", "c1" -> "chain")(bc0, bc1)
    val fe = Rule(g1, g2, Map("b" -> "b", "c1" -> "c1", "c2" -> "c2"),
      Map(c1c2 -> c1c2, bc1 -> bc1), 1)
    val fc = Rule(g2, g3, Map("b" -> "b", "c1" -> "c1", "c2" -> "c2"),
      Map(c1c2 -> c1c2, bc2 -> bc2), 100)
    val bc = fe.reversed; bc.rate = 10
    val be = fc.reversed; be.rate = 1000

    object mfa extends MFA[String,String] {

      // Transformations
      def invariant(g: G): Option[P] =
        if (Graph.iso(g, g1) || Graph.iso(g, g3)) Some(1.0 * g4)
        else None

      def reachable(g: G): Option[P] = {
        val bs = g.nodes collect { case n if g(n).label == Some("bimotor") => n }
        val cs = g.nodes collect { case n if g(n).label == Some("chain") => n }
        if ((bs.size == 1) && (bs forall (g(_).outDegree == 2)) &&
            (cs.size <= 2) && (cs.toSeq.combinations(2) forall {
              case Seq(u, v) => ((g(u) edgesWith v).size == 1) }))
          None
        else Some(Pn.empty)
      }
    }

    val eqs = mfa.mfa(List(fe, fc, bc, be), List(g1, g2, g3),
      mfa.invariant _, mfa.reachable _)
    eqs.printEqs
  }
}

