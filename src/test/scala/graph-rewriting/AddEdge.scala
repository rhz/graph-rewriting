package graph_rewriting

import graph_rewriting.RewritingSystem._
import Implicits._

object AddEdgeTest {

  type L = String

  // Outer nodes
  val a = Node("a:A")
  val b = Node("b:B")

  // Graphs
  val g1 = Graph[Node,EqDiEdge](a, b)
  val g2 = Graph[Node,EqDiEdge](a~>b)

  val add = Rule(g1, g2)((g1.nodes, g2.nodes).zipped.toMap, Map(), 1.0)

  // def main(args: Array[String]) = {
  //   val eqs = mfa[L](List(add), List(g2))
  //   for (eq <- eqs) println(eq)
  //   println()
  //   val simpEqs = eqs map (eq => eq match {
  //     case AlgEquation(lhs, rhs) => AlgEquation(lhs, rhs.simplify[L])
  //     case ODE(lhs, rhs) => ODE(lhs, rhs.simplify[L])
  //   })
  //   for (eq <- simpEqs) println(eq)
  //   println()
  //   printEqs(simpEqs)
  // }
}
