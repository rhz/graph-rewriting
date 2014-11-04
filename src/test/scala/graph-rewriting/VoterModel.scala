package graph_rewriting

import implicits._
import meanfield._

object VoterModel {
  def main(args: Array[String]): Unit = {
    val (e1, e2) = ("u" ~~> "v", "u" ~~> "w")
    val rb = Graph("u" -> "red", "v" -> "blue")(e1)
    val bb = Graph("u" -> "blue", "v" -> "blue")(e1)
    val rr = Graph("u" -> "red", "v" -> "red")(e1)
    // val w = Graph("w")() // for flapping
    // Flipping rules
    val r2b = Rule(rb, rr, 1)
    val b2r = Rule(rb, bb, 10)
    // Flapping rules
    // Observables
    val r = Graph("u" -> "red")()
    // Fragmentation
    val eqs = mfa(List(r2b, b2r), List(r))
    eqs.printEqs
  }
}

