package graph_rewriting

import graph_rewriting.RewritingSystem._
import Implicits._

object BiWalker {

  type L = String

  // Outer nodes
  val b = Node("b:bimotor")
  val c1 = Node("c1:chain")
  val c2 = Node("c2:chain")

  // Graphs
  val g1 = Graph(b~>c1, b~>c1, c1~>c2)
  val g2 = Graph(b~>c1, b~>c2, c1~>c2)
  val g3 = Graph(b~>c2, b~>c2, c1~>c2)
  val g4 = Graph(b~>c1, b~>c1)

  // Inner edges
  val g1c1c2 = findEdge(g1, c1~>c2).get
  val g2c1c2 = findEdge(g2, c1~>c2).get
  val g3c1c2 = findEdge(g3, c1~>c2).get
  val g1bc1 = findEdge(g1, b~>c1).get
  val g2bc1 = findEdge(g2, b~>c1).get
  val g2bc2 = findEdge(g2, b~>c2).get
  val g3bc2 = findEdge(g3, b~>c2).get

  // Rates
  val k1 = 1.0
  val k2 = 100.0

  // Rules
  val fe = Rule(g1, g2)((g1.nodes, g2.nodes).zipped.toMap,
    Map(g1c1c2 -> g2c1c2, g1bc1 -> g2bc1), k1)
  val fc = Rule(g2, g3)((g2.nodes, g3.nodes).zipped.toMap,
    Map(g2c1c2 -> g3c1c2, g2bc2 -> g3bc2), k2)
  val bc = fe.reversed
  val be = fc.reversed

  // Transformations
  def invariant(g: Graph): Option[Polynomial] = {
    val h = GraphWrapper(g)
    if (h.isIsoTo[L](g1) || h.isIsoTo[L](g3)) Some(1.0 * g4)
    else None
  }

  def reachable(g: Graph): Option[Polynomial] = {
    // TODO: Filter loops or maybe just filter anything with
    // n.inDegree + n.outDegree >= 2
    val nodesByLabel = g.nodes groupBy (_.label)
    if ((!(nodesByLabel contains "bimotor") ||
          ((nodesByLabel("bimotor").size == 1) &&
           (nodesByLabel("bimotor").head.outDegree == 2))) &&
        (!(nodesByLabel contains "chain") ||
          (nodesByLabel("chain") forall (n =>
            (n.incoming.filter(_.source.label == "chain").size +
             n.outgoing.filter(_.target.label == "chain").size) <= 1)))) {
      println("reachable found: " + g)
      None
    } else Some(Polynomial(Vector()))
  }

  // def main(args: Array[String]) = {

    // println()

    // invariant(g1) match {
    //   case Some(p) => {
    //     println("g1: " + p)
    //     println("g1 simplified: " + p.simplify[L])
    //   }
    //   case None =>
    //     throw new Exception("g1 is not isomorphic to itself")
    // }
    // println()

    // minimal glueings with the left-hand side
    // val deletions: Seq[Monomial] =
    //   for ((mg, _, _) <- unions(g2, fe.lhs)) yield -1.0 * fe.rate * mg

    // minimal glueings with the right-hand side
    // val feOpp: Rule = fe.reversed
    // println()
    // val additions: Seq[Monomial] =
    //   for ((mg, _, m) <- unions(g2, feOpp.dom)) yield {
    //     feOpp(m)
    //     feOpp.rate * mg
    //   }

    // println("deletions:")
    // for (d <- deletions) println("  " + d)
    // println()
    // println("additions:")
    // for (a <- additions) println("  " + a)
    // println()

    // val p = Polynomial((deletions ++ additions).toVector)
    // println("g2 simplified:")
    // for (m <- p.simplify[L].terms) println("  " + m)
    // println()

    // val (mg, _, m) = unions(g2, feOpp.dom).head
    // println(mg)
    // feOpp(m)
    // println(mg)



    val eqs = mfa[L](3, List(fe, fc, bc, be), List(g1, g2, g3),
      invariant _, reachable _)
    // for (eq <- eqs) println(eq)
    // println()
    // val simpEqs = eqs map (eq => eq match {
    //   case AlgEquation(lhs, rhs) => AlgEquation(lhs, rhs.simplify[L])
    //   case ODE(lhs, rhs) => ODE(lhs, rhs.simplify[L])
    // })
    // for (eq <- simpEqs) println(eq)
    // println()
    printEqs[L](eqs)
  // }
}
