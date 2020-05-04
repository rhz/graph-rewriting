package hz.ricardo
package graph_rewriting

import moments._

object IrreversibleMarks {
  type N = String
  type E = IdDiEdge[Int,N]
  type NL = String
  type EL = String
  val G = MarkedDiGraph.withType[N,NL,E,EL]
  // https://www.scala-lang.org/files/archive/spec/2.13/07-implicits.html
  // the next line shouldn't be necessary according to the spec
  implicit val graphBuilder = MarkedDiGraph.empty[N,NL,E,EL] _
  def main(args: Array[String]): Unit = {
    val e1 = "B"~~>"A"
    val g1 = G("A")()
    val g2 = G("A","B")(e1)
    // Death rule: A =>
    val death = Rule(g1,G()(),Map(),Map(),"kD")

    val odes = generateMeanODEs(2,
      List(death),
      List(g1.copy.mark("A"),g2.copy.mark("A")))
    val p = ODEPrinter(odes)
    p.print
  }
}

