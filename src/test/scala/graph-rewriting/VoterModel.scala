package hz.ricardo
package graph_rewriting

import moments._

object VoterModel {
  type N = String
  type E = IdDiEdge[Int,N]
  type NL = String
  type EL = String
  val G = DiGraph.withType[N,NL,E,EL]
  // https://www.scala-lang.org/files/archive/spec/2.13/07-implicits.html
  // the next line shouldn't be necessary according to the spec
  implicit val graphBuilder = DiGraph.empty[N,NL,E,EL] _
  def main(args: Array[String]): Unit = {
    // first flip
    val e = "u"~~>"v"
    val rb = G("u"->"red","v"->"blue")(e)
    val br = G("u"->"blue","v"->"red")(e)
    val bb = G("u"->"blue","v"->"blue")(e)
    val k01 = Rate("k01", 0.9)
    val flip0a = Rule(rb, bb, Map("u"->"u","v"->"v"),
      Map(e->e), k01)
    val flip0b = Rule(br, bb, Map("u"->"u","v"->"v"),
      Map(e->e), k01)
    // second flip
    val rr = G("u"->"red","v"->"red")(e)
    val k10 = Rate("k10", 1.1)
    val flip1a = Rule(rb, rr, Map("u"->"u","v"->"v"),
      Map(e->e), k10)
    val flip1b = Rule(br, rr, Map("u"->"u","v"->"v"),
      Map(e->e), k10)
    // first swap (blue rewire)
    val rbw1 = G("u"->"red","v"->"blue","w")("u"~~>"v")
    val rbw2 = G("u"->"red","v"->"blue","w")("w"~~>"v")
    val swap0a = Rule(rbw1, rbw2, Map("u"->"u","v"->"v","w"->"w"),
      Map(), "k0")
    val brw1 = G("u"->"blue","v"->"red","w")("u"~~>"v")
    val brw2 = G("u"->"blue","v"->"red","w")("w"~~>"u")
    val swap0b = Rule(brw1, brw2, Map("u"->"u","v"->"v","w"->"w"),
      Map(), "k0")
    // second swap (red rewire)
    val rbw3 = G("u"->"red","v"->"blue","w")("w"~~>"u")
    val swap1a = Rule(rbw1, rbw3, Map("u"->"u","v"->"v","w"->"w"),
      Map(), "k1")
    val brw3 = G("u"->"blue","v"->"red","w")("w"~~>"v")
    val swap1b = Rule(brw1, brw3, Map("u"->"u","v"->"v","w"->"w"),
      Map(), "k1")
    def pairApproximation(g: DiGraph[N,NL,E,EL]): Option[Pn[N,NL,E,EL,DiGraph]] =
      if (g.nodes.size == 3 && g.edges.size == 2 && g.isConnected) {
        val List(e1, e2) = g.edges.toList
        val intersection = e1.nodes &~ (e1.nodes &~ e2.nodes)
        Some(Pn(Mn(g.inducedSubgraph(e1.nodes)) *
                   g.inducedSubgraph(e2.nodes) /
                   g.inducedSubgraph(intersection)))
      } else None
    def noParallelEdges(g: DiGraph[N,NL,E,EL]): Option[Pn[N,NL,E,EL,DiGraph]] =
      if (g.nodes.size == 2 && g.edges.size == 2) Some(Pn.zero) else None
    val redNode = G("u" -> "red")()
    val twoRedNodes = G("u" -> "red", "v" -> "red")()
    val odesWoTrans = generateMeanODEs(2,
      List(flip0a,flip0b,flip1a,flip1b,swap0a,swap0b,swap1a,swap1b),
      List(redNode))
    ODEPrinter(odesWoTrans).print
    println()
    val odes = generateMeanODEs(10,
      List(flip0a,flip0b,flip1a,flip1b,swap0a,swap0b,swap1a,swap1b),
      List(G("u"->"red","v"->"blue")("u"~~>"v")), //redNode),
      splitConnectedComponents[N,NL,E,EL,DiGraph] _,
      pairApproximation _,
      noParallelEdges _)
    val printer = ODEPrinter(odes)
    printer.print
    // printer.saveAsOctave("voter.m", 0.04, 1000,
    //   List(50.0,50,50,50,50,50,100)) // [0],[01],[10],[1],[00],[11],[*]
    println()
    val varianceODE = generateMeanODEs(1,
      List(flip0a,flip0b,flip1a,flip1b,swap0a,swap0b,swap1a,swap1b),
      List(twoRedNodes))
    ODEPrinter(varianceODE).print
  }
}

