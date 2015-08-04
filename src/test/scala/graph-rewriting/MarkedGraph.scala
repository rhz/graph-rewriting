package uk.ac.ed.inf
package graph_rewriting

import org.scalatest.{FlatSpec, Matchers}

class MarkedDiGraphSpec extends FlatSpec with Matchers {

  type N1 = Int
  type NL = String
  type E1 = IdDiEdge[Int,N1]
  type EL = String
  val G = MarkedDiGraph.withType[N1,NL,E1,EL]

  "A marked graph" should "add marks on nodes only once" in {
    val e = 0~~>1
    val g = G(0->"label",1)(e)
    g.nodes shouldBe Set(0,1)
    g.edges shouldBe Set(e)
    g.nodelabels shouldBe Map(0->"label")
    g.edgelabels shouldBe empty
    g.adjacency shouldBe
      Map(0 -> Map(e -> Set(1)),
          1 -> Map(e -> Set(0)))
    g(0).marked shouldBe false
    g(1).marked shouldBe false
    // g.markedNodes shouldBe empty
    g(0).mark
    g(0).marked shouldBe true
    g(1).marked shouldBe false
    // g.markedNodes shouldBe Set(0)
    g(0).mark
    g(0).marked shouldBe true
    g(1).marked shouldBe false
    // g.markedNodes shouldBe Set(0)
    g(0).unmark
    g(0).marked shouldBe false
    g(1).marked shouldBe false
    // g.markedNodes shouldBe empty
  }

  it should "tell if it is a subgraph of another graph" in {
    val e = 0~~>1
    val g1 = G(0->"label",1)(e)
    val g2 = G(0,1)()
    assert(g2 subgraphOf g1)
    g2 += e
    assert(g2 subgraphOf g1)
    g2 += (0~~>1)
    assert(!g2.subgraphOf(g1))
  }

  it should "construct induced subgraphs" in {
    val e1 = 0~~>1
    val e2 = 1~~>0
    val e3 = 1~~>2
    val g1 = G(0,1,2)(e1,e2,e3)
    val g2 = g1.inducedSubgraph(0,1)
    g2.nodes shouldBe Set(0,1)
    g2.edges shouldBe Set(e1,e2)
    assert(g2 subgraphOf g1)
    val g3 = g1.inducedSubgraph(1,2)
    g3.nodes shouldBe Set(1,2)
    g3.edges shouldBe Set(e3)
    assert(g3 subgraphOf g1)
  }

  it should "compute its disjoint sets" in {
    val e1 = 0~~>1
    val e2 = 1~~>2
    val g = G(0,1,2)(e1,e2)
    val ps = g.parents
    all (ps.values map (g.findRoot(_,ps))) shouldEqual
      g.findRoot(ps.values.head,ps)
  }

  it should "compute its connected components" in {
    val e1 = 0~~>1
    val e2 = 1~~>0
    val e3 = 1~~>2
    val g1 = G(0,1,2,3,4)(e1,e2,3~~>4)
    val g2 = g1.inducedSubgraph(0,1)
    val g3 = g1.inducedSubgraph(2)
    val g4 = g1.inducedSubgraph(3,4)
    g1.components.toSet shouldBe Set(g2,g3,g4)
    g1 += e3
    val g5 = g1.inducedSubgraph(0,1,2)
    g1.components.toSet shouldBe Set(g4,g5)
  }

  it should "tell if it is isomorphic to another graph" in {
    import MarkedDiGraph._
    val g1 = G(0,1,2)(0~~>1,1~~>0,1~~>2)
    val g2 = G(3,4,5)(5~~>4,4~~>5)
    assert(!g1.iso(g2))
    g2 += (4~~>3)
    assert(g1 iso g2)
    g2 += 0
    assert(!g1.iso(g2))

    val g3 = G(0,2,1)(0~~>1,0~~>2).inMark(2)
    val g4 = G(0,1,2)(0~~>1,0~~>2).inMark(2)
    assert(g3 iso g4)
  }

  type N2 = String
  type E2 = IdDiEdge[Int,N2]
  val M = MarkedDiGraph.withType[N2,NL,E2,EL]
  val c1c2 = "c1"~~>"c2"
  val bc1 = "b"~~>"c1"
  val bc2 = "b"~~>"c2"
  val bc3 = "b"~~>"c1"

  it should "compute intersections with other graphs" in {
    val g1 = M("b"->"bimotor","c1"->"chain","c2"->"chain")(bc1,c1c2,bc2).mark("b")
    val g2 = M("b"->"bimotor","c1"->"chain","c2"->"chain")(bc1,c1c2,bc3).mark("b")
    val pbs = for ((pb,_,_) <- g1.intersections[N2,E2,N2,E2,MarkedDiGraph](g2)) yield pb
    /* TODO: What are the intersections like with marked graphs?
    pbs.length shouldBe 8
    pbs(0) shouldBe empty
    pbs(1) shouldBe M("(c2,c2)" -> "chain")()
    pbs(2) shouldBe M("(c2,c1)" -> "chain")()
    pbs(3) shouldBe M("(c1,c2)" -> "chain")()
    pbs(4) shouldBe M("(c1,c1)" -> "chain")()
    pbs(5) shouldBe M("(c1,c1)" -> "chain", "(c2,c2)" -> "chain")()
    assert(pbs(6) iso M("(c1,c1)" -> "chain",
      "(c2,c2)" -> "chain")("(c1,c1)" ~~> "(c2,c2)"))
    pbs(7) shouldBe M("(c1,c2)" -> "chain", "(c2,c1)" -> "chain")()
    */
  }

  /*
  it should "compute unions with other graphs" in {
    val g1 = M("b"->"bimotor","c1"->"chain","c2"->"chain")(bc1,c1c2,bc2)
      .mark("b")
    val g2 = M("b"->"bimotor","c1"->"chain","c2"->"chain")(bc1,c1c2,bc3)
      .mark("b")
    val pos = for ((po,_,_) <- g1.unions[N2,E2,N2,E2,MarkedDiGraph](g2)) yield po
    pos.length shouldBe 8
    assert(pos(0) iso M(
      "(b,)" -> "bimotor", "(c1,)" -> "chain", "(c2,)" -> "chain",
      "(,b)" -> "bimotor", "(,c1)" -> "chain", "(,c2)" -> "chain")(
      "(b,)" ~~> "(c1,)", "(b,)" ~~> "(c2,)", "(c1,)" ~~> "(c2,)",
        "(,b)" ~~> "(,c1)", "(,b)" ~~> "(,c1)", "(,c1)" ~~> "(,c2)")
      .mark("(b,)", "(,b)"))
    assert(pos(1) iso M(
      "(b,)" -> "bimotor", "(c1,)" -> "chain", "(c2,c2)" -> "chain",
      "(,b)" -> "bimotor", "(,c1)" -> "chain")(
      "(b,)" ~~> "(c1,)", "(b,)" ~~> "(c2,c2)", "(c1,)" ~~> "(c2,c2)",
      "(,b)" ~~> "(,c1)", "(,b)" ~~> "(,c1)", "(,c1)" ~~> "(c2,c2)")
      .mark("(b,)", "(,b)"))
    assert(pos(2) iso M(
      "(b,)" -> "bimotor", "(c1,)" -> "chain", "(c2,c1)" -> "chain",
      "(,b)" -> "bimotor", "(,c2)" -> "chain")(
      "(b,)" ~~> "(c1,)", "(b,)" ~~> "(c2,c1)", "(c1,)" ~~> "(c2,c1)",
      "(,b)" ~~> "(c2,c1)", "(,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(,c2)")
      .mark("(b,)", "(,b)"))
    assert(pos(3) iso M(
      "(b,)" -> "bimotor", "(c1,c2)" -> "chain", "(c2,)" -> "chain",
      "(,b)" -> "bimotor", "(,c1)" -> "chain")(
      "(b,)" ~~> "(c1,c2)", "(b,)" ~~> "(c2,)", "(c1,c2)" ~~> "(c2,)",
      "(,b)" ~~> "(,c1)", "(,b)" ~~> "(,c1)", "(,c1)" ~~> "(c1,c2)")
      .mark("(b,)", "(,b)"))
    assert(pos(4) iso M(
      "(b,)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,)" -> "chain",
      "(,b)" -> "bimotor", "(,c2)" -> "chain")(
      "(b,)" ~~> "(c1,c1)", "(b,)" ~~> "(c2,)", "(c1,c1)" ~~> "(c2,)",
      "(,b)" ~~> "(c1,c1)", "(,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(,c2)")
      .mark("(b,)", "(,b)"))
    assert(pos(5) iso M(
      "(b,)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain",
      "(,b)" -> "bimotor")(
      "(b,)" ~~> "(c1,c1)", "(b,)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(,b)" ~~> "(c1,c1)", "(,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(c2,c2)")
      .mark("(b,)", "(,b)"))
    assert(pos(6) iso M(
      "(b,)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain",
      "(,b)" -> "bimotor")(
      "(b,)" ~~> "(c1,c1)", "(b,)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(,b)" ~~> "(c1,c1)", "(,b)" ~~> "(c1,c1)")
      .mark("(b,)", "(,b)"))
    assert(pos(7) iso M(
      "(b,)" -> "bimotor", "(c1,c2)" -> "chain", "(c2,c1)" -> "chain",
      "(,b)" -> "bimotor")(
      "(b,)" ~~> "(c1,c2)", "(b,)" ~~> "(c2,c1)", "(c1,c2)" ~~> "(c2,c1)",
      "(,b)" ~~> "(c2,c1)", "(,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(c1,c2)")
      .mark("(b,)", "(,b)"))
  }
  */
}

