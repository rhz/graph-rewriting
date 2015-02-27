package graph_rewriting

import implicits._
import meanfield._ // this imports types N = String and E = IdDiEdge[Int, N]

object Rabbits {
  val G = Graph.withType[N,String,E,String]
  def main(args: Array[String]): Unit = {
    val (e1, e2) = ("father" ~~> "daughter", "mother" ~~> "daughter")
    val parents = G("father" -> "R", "mother" -> "R")()
    val one = G("father" -> "R", "mother" -> "R", // one child
      "daughter" -> "R")(e1, e2)
    val sex = Rule(parents, one, Map("father" -> "father",
      "mother" -> "mother"), Map(), "k1")
    val two = G("father" -> "R", "mother" -> "R", "daughter" -> "R", // two children
      "son" -> "R")(e1, e2, "father" ~~> "son", "mother" ~~> "son")
    val family = Rule(one, two, Map("father" -> "father",
      "mother" -> "mother", "daughter" -> "daughter"),
      Map(e1 -> e1, e2 -> e2), "k2")
    val eqs = mfa(List(sex, family), List(two),
      splitConnectedComponents[N,String,E,String] _)
    ODEPrinter(eqs).print
    ODEPrinter(eqs).saveAsOctave("rabbits.m", 0.7, 1000,
      g => if (Graph.iso(g, G("rabbit" -> "R")())) 1.0 else 0.0)
  }
}

