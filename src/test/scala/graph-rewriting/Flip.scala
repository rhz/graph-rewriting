package graph_rewriting

import graph_rewriting.RewritingSystem._
import Implicits._

object Flip {

  type L = String

  val a1 = Node("a1")
  val a2 = Node("a2")
  val b1 = Node("b1")
  val b2 = Node("b2")

  val a1Loop = (a1 ~+> a1)("A")
  val a2Loop = (a2 ~+> a2)("A")
  val b1Loop = (b1 ~+> b1)("B")
  val b2Loop = (b2 ~+> b2)("B")

  val k1 = 1.0
  val k2 = 100.0

  val aa = Graph(a1~>a2, a1Loop, a2Loop)
  val ab = Graph(a1~>b1, a1Loop, b1Loop)
  val bb = Graph(b2~>b1, b1Loop, b2Loop)

  val aa_a1a2 = findEdge(aa, a1~>a2).get
  val aa_a1Loop = findEdge(aa, a1Loop).get
  val aa_a2Loop = findEdge(aa, a2Loop).get
  val ab_a1b1 = findEdge(ab, a1~>b1).get
  val ab_a1Loop = findEdge(ab, a1Loop).get
  val ab_b1Loop = findEdge(ab, b1Loop).get
  val bb_b1b2 = findEdge(bb, b2~>b1).get
  val bb_b1Loop = findEdge(bb, b1Loop).get
  val bb_b2Loop = findEdge(bb, b2Loop).get

  // FIXME!
  // val flipA = Rule(ab, bb)((ab.nodes zip bb.nodes).toMap,
  //   Map(ab.edges.head -> bb.edges.head), k1)
  // val flipB = Rule(ab, aa)((ab.nodes zip aa.nodes).toMap,
  //   Map(ab.edges.head -> aa.edges.head), k2)
  val flipA = Rule(ab, bb)(
    Map(ab.get(a1) -> bb.get(b2),
        ab.get(b1) -> bb.get(b1)),
    Map(ab_a1b1 -> bb_b1b2,
        ab_b1Loop -> bb_b1Loop),
    k1)
  // val flipB = Rule(ab, aa)(
  //   Map(ab.get(a1) -> aa.get(a1), ab.get(b1) -> aa.get(a2)),
  //   Map(ab_a1b1 -> aa_a1a2, ab_a1Loop -> aa_a1Loop),
  //   k2)

  def simple(g: Graph): Option[Polynomial] =
    if (g.nodes forall (n => n.edges.size == (n.neighbors.size + 1))) None
    else {
      println("not simple: " + g)
      Some(Polynomial(Vector()))
    }

  // def main(args: Array[String]) = {
  //   val eqs = mfa[L](5, List(flipA), List(ab), simple _)
  //   printEqs(eqs)
  // }
}
