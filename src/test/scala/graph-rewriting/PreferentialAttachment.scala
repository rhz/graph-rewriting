package uk.ac.ed.inf
package graph_rewriting

import moments._

object PreferentialAttachment {
  // TODO: Use type N = Int
  type N = String
  type E = IdDiEdge[Int,N]
  type NL = String
  type EL = String
  val G = MarkedDiGraph.withType[N,NL,E,EL]
  def main(args: Array[String]): Unit = {
    val e1 = "B"~~>"A"
    val e2 = "C"~~>"A"
    val g1 = G("A")()
    val g2 = G("A","B")(e1)
    val g3 = G("A","B","C")(e1,e2)
    // Birth rule: A => A <- B
    val birth = Rule(g1,g2.copy.mark("B"),
      Map("A"->"A"),Map(),"kB")
    // Preferential attachment rule: B -> A => B -> A <- C
    val pa = Rule(g2,g3.copy.mark("C"),
      Map("A"->"A","B"->"B"),Map(e1->e1),"kP")
    // Death rule: A =>
    val death = Rule(g1,G()(),Map(),Map(),"kD")

    def N(i: Int): MarkedDiGraph[N,NL,E,EL] =
      G(for (j <- 0 to i) yield s"$j",
        for (j <- 1 to i) yield s"$j"~~>"0").inMark("0")

    // for ((pb,_,_,po,_,_) <- N(3).intersectionsAndUnions[N,E,N,E,MarkedDiGraph](N(3))) {
    //   println(pb)
    //   println(po)
    //   println()
    // }
    // for ((pb,_,_,po,_,_) <- g3.intersectionsAndUnions[N,E,N,E,MarkedDiGraph](N(0))) {
    //   println(pb)
    //   println(po)
    //   println()
    // }

    val odes = generateMeanODEs(10,
      List(birth,pa,death),
      List(g1,g2,g3)) //,N(0),N(1)))
    val p = ODEPrinter(odes)
    p.print
    // p.saveAsOctave("pa.m", 5.0, 1000,
    //   g => if (g eq g1) 1.0 else 0.0)
  }
}

