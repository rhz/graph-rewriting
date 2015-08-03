package graph_rewriting

import implicits._
import moments._

object Bimotor {
  type N = String
  type E = IdDiEdge[Int,N]
  type NL = String
  type EL = String
  val G = DiGraph.withType[N,NL,E,EL]
  def main(args: Array[String]): Unit = {
    val bc0 = "b" ~~> "c1"
    val bc1 = "b" ~~> "c1"
    val bc2 = "b" ~~> "c2"
    val bc3 = "b" ~~> "c2"
    val c1c2 = "c1" ~~> "c2"
    val g1 = G("b"->"bimotor","c1"->"chain","c2"->"chain")(bc0,bc1,c1c2)
    val g2 = G("b"->"bimotor","c1"->"chain","c2"->"chain")(bc1,bc2,c1c2)
    val g3 = G("b"->"bimotor","c1"->"chain","c2"->"chain")(bc2,bc3,c1c2)
    val g4 = G("b"->"bimotor","c1"->"chain")(bc0,bc1)
    val fe = Rule(g1, g2, Map("b"->"b","c1"->"c1","c2"->"c2"),
      Map(c1c2->c1c2,bc1->bc1), "kFE")
    val fc = Rule(g2, g3, Map("b"->"b","c1"->"c1","c2"->"c2"),
      Map(c1c2->c1c2,bc2->bc2), "kFC")
    val bc = fe.reversed("kBC")
    val be = fc.reversed("kBE")

    // Transformations
    def invariant(g: DiGraph[N,NL,E,EL]): Option[Pn[N,NL,E,EL,DiGraph]] =
      if (g.iso(g1) || g.iso(g3)) Some(Pn(Mn(g4))) else None

    def reachable(g: DiGraph[N,NL,E,EL]): Option[Pn[N,NL,E,EL,DiGraph]] = {
      val bs = g.nodes collect {
        case n if g(n).label == Some("bimotor") => n }
      val cs = g.nodes collect {
        case n if g(n).label == Some("chain") => n }
      if ((bs.size == 1) && (bs forall (g(_).outDegree == 2)) &&
          (cs.size <= 2) && (cs.toSeq.combinations(2) forall {
            case Seq(u,v) => ((g(u) edgesWith v).size == 1) }))
        None
      else Some(Pn.zero)
    }

    val odes = generateMeanODEs(5,
      List(fe,fc,bc,be),
      List(g1,g2,g3),
      invariant _,
      reachable _)
    ODEPrinter(odes).print
    ODEPrinter(odes).saveAsOctave("bimotor.m", 5.0, 1000,
      g => if (g eq g4) 1.0 else 0.0)
  }
}

