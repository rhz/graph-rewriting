package graph_rewriting

import implicits._
import meanfield._ // this imports types N = String and E = IdDiEdge[Int, N]

object Rabbits {
  def main(args: Array[String]): Unit = {
    val k1 = 1.0
    val (e1, e2) = ("father" ~~> "daughter", "mother" ~~> "daughter")
    val parents = Graph("father" -> "R", "mother" -> "R")()
    val one = Graph("father" -> "R", "mother" -> "R", // one child
      "daughter" -> "R")(e1, e2)
    val sex = Rule(parents, one, Map("father" -> "father",
      "mother" -> "mother"), Map(), k1)
    val two = Graph("father" -> "R", "mother" -> "R", "daughter" -> "R",
      "son" -> "R")(e1, e2, "father" ~~> "son", "mother" ~~> "son")
    val family = Rule(one, two, Map("father" -> "father",
      "mother" -> "mother", "daughter" -> "daughter"),
      Map(e1 -> e1, e2 -> e2), 10)
    val eqs = mfa(List(sex, family), List(two),
      splitConnectedComponents[N,String,E,String] _)
    eqs.printEqs
  }
}

