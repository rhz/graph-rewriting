package graph_rewriting

import graph_rewriting.RewritingSystem._
import Implicits._

object Rabbits {

  type L = String

  // Outer nodes
  val p1 = Node("father")
  val p2 = Node("mother")
  val c1 = Node("son")
  val c2 = Node("daughter")

  // Graphs
  val onlyParents = Graph[Node,EqDiEdge](p1, p2)
  val oneChild = Graph(p1~>c1, p2~>c1)
  val twoChild = Graph(p1~>c1, p2~>c1, p1~>c2, p2~>c2)

  // Inner nodes
  val p1in1 = onlyParents get p1
  val p2in1 = onlyParents get p2
  val p1in2 = oneChild get p1
  val p2in2 = oneChild get p2

  // Inner edges
  val p1c1 = findEdge(oneChild, p1~>c1).get
  val p2c1 = findEdge(oneChild, p2~>c1).get

  // Rates
  val k1 = 1.0

  // Rules
  val sex = Rule[L](onlyParents, oneChild)(
    Map(p1in1 -> p1in2, p2in1 -> p2in2), Map(), k1)

  // Transformations
  def nonDerivable(g: Graph): Option[Polynomial] =
    if ((g.edges.toSeq.combinations(2).toSeq forall {
          case (e1 +: e2 +: _) =>
            (e1.source == e2.source) && (e1.target == e2.target) }) &&
        (g.nodes forall (n => (n.diPredecessors.size == 2) ||
          (n.diPredecessors.size == 2))))
      Some(Polynomial(Vector()))
    else None

  def main(args: Array[String]) = {
    val eqs = mfa[L](List(sex), List(twoChild), splitConnectedComponents, nonDerivable _)
    printEqs[L](eqs)
  }
}
