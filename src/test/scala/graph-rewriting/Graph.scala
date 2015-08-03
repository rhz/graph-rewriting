package graph_rewriting

import org.scalatest.{FlatSpec, Matchers}
import implicits._

class GraphSpec extends FlatSpec with Matchers {

  type N1 = Int
  type E1 = DiEdge[N1]
  type NL = String
  type EL = String
  type SimpleGraph = DiGraph[N1,NL,E1,EL]

  "A simple graph" should "add same node only once" in {
    val g = new SimpleGraph
    g.nodes shouldBe empty
    g.edges shouldBe empty
    g.nodelabels shouldBe empty
    g.edgelabels shouldBe empty
    g.adjacency shouldBe empty
    g += 1
    g.nodes shouldBe Set(1)
    g.edges shouldBe empty
    g += 0
    g.nodes shouldBe Set(0,1)
    g.edges shouldBe empty
    g += 0
    g.nodes shouldBe Set(0,1)
    g.edges shouldBe empty
    g.nodelabels shouldBe empty
    g.edgelabels shouldBe empty
    g.adjacency.keySet shouldBe Set(0,1)
    all (g.adjacency.values) shouldBe empty
  }

  it should "add nodes in bulk" in {
    val g = new SimpleGraph
    g.nodes shouldBe empty
    g.edges shouldBe empty
    g.addNodes(2,3)
    g.nodes shouldBe Set(2,3)
    g.edges shouldBe empty
  }

  val e1 = DiEdge(4,5)
  val e2 = DiEdge(5,4)

  it should "add same edge only once" in {
    val g = new SimpleGraph
    g.addNodes(4,5)
    g += e1
    g.nodes shouldBe Set(4,5)
    g.edges shouldBe Set(e1)
    g += e2
    g.nodes shouldBe Set(4,5)
    g.edges shouldBe Set(e1,e2)
    g += e1
    g.nodes shouldBe Set(4,5)
    g.edges shouldBe Set(e1,e2)
    g.nodelabels shouldBe empty
    g.edgelabels shouldBe empty
    for ((k,v) <- g.adjacency) k match {
      case 4 => v shouldBe Map(e1 -> Set(5), e2 -> Set(5))
      case 5 => v shouldBe Map(e1 -> Set(4), e2 -> Set(4))
    }
  }

  it should "add edges in bulk" in {
    val g = new SimpleGraph
    g.addNodes(4,5)
    g.addEdges(e1,e2)
    g.nodes shouldBe Set(4,5)
    g.edges shouldBe Set(e1,e2)
  }

  it should "add labels to nodes" in {
    val g = new SimpleGraph
    g.addNodes(4,5)
    g.addEdges(e1,e2)
    g(4).label shouldBe None
    g(5).label shouldBe None

    g(4).label = "node 4"
    g(4).label shouldBe Some("node 4")
    g(5).label shouldBe None

    g(5).label = "node 5"
    g(4).label shouldBe Some("node 4")
    g(5).label shouldBe Some("node 5")

    // adding node labels should not add nodes or edges
    g.nodes shouldBe Set(4,5)
    g.edges shouldBe Set(e1,e2)
  }

  it should "add labels to edges" in {
    val g = new SimpleGraph
    g.addNodes(4,5)
    g.addEdges(e1,e2)
    g(e1).label shouldBe None
    g(e2).label shouldBe None

    g(e1).label = "edge 1"
    g(e1).label shouldBe Some("edge 1")
    g(e2).label shouldBe None

    g(e2).label = "edge 2"
    g(e1).label shouldBe Some("edge 1")
    g(e2).label shouldBe Some("edge 2")

    // adding edge labels should not add nodes or edges
    g.nodes shouldBe Set(4,5)
    g.edges shouldBe Set(e1,e2)
  }

  it should "be constructible" in {

    val g0 = DiGraph.empty[N1,NL,E1,EL]
    g0.nodes shouldBe empty
    g0.edges shouldBe empty
    g0.nodelabels shouldBe empty
    g0.edgelabels shouldBe empty
    g0.adjacency shouldBe empty

    // val g1 = Graph(List(4 -> "node 4", 5 -> "node 5"),
    //                List(e1 -> "edge 1", e2 -> "edge 2"))
    // g1.nodes shouldBe Set(4, 5)
    // g1.edges shouldBe Set(e1, e2)
    // g1.nodelabels shouldBe Map(4 -> "node 4", 5 -> "node 5")
    // g1.edgelabels shouldBe Map(e1 -> "edge 1", e2 -> "edge 2")
    // for ((k, v) <- g1.adjacency) k match {
    //   case 4 => v shouldBe Map(e1 -> Set(5), e2 -> Set(5))
    //   case 5 => v shouldBe Map(e1 -> Set(4), e2 -> Set(4))
    // }

    val g2 = DiGraph(4,5)()
    g2.nodes shouldBe Set(4,5)
    g2.edges shouldBe empty
    g2.nodelabels shouldBe empty
    g2.edgelabels shouldBe empty
    g2.adjacency.keySet shouldBe Set(4,5)
    all (g2.adjacency.values) shouldBe empty

    val g3 = DiGraph(4,5)(e1,e2)
    g3.nodes shouldBe Set(4,5)
    g3.edges shouldBe Set(e1,e2)
    g3.nodelabels shouldBe empty
    g3.edgelabels shouldBe empty
    for ((k,v) <- g3.adjacency) k match {
      case 4 => v shouldBe Map(e1 -> Set(5), e2 -> Set(5))
      case 5 => v shouldBe Map(e1 -> Set(4), e2 -> Set(4))
    }

    val g4 = DiGraph(4,5)(e1 -> 1, e2 -> 2)
    g4.nodes shouldBe Set(4,5)
    g4.edges shouldBe Set(e1,e2)
    g4.nodelabels shouldBe empty
    g4.edgelabels shouldBe Map(e1 -> 1, e2 -> 2)
    for ((k,v) <- g4.adjacency) k match {
      case 4 => v shouldBe Map(e1 -> Set(5), e2 -> Set(5))
      case 5 => v shouldBe Map(e1 -> Set(4), e2 -> Set(4))
    }

    val g5 = DiGraph(4 -> "node 1", 5 -> "node 2")()
    g5.nodes shouldBe Set(4,5)
    g5.edges shouldBe empty
    g5.nodelabels shouldBe Map(4 -> "node 1", 5 -> "node 2")
    g5.edgelabels shouldBe empty
    g5.adjacency.keySet shouldBe Set(4,5)
    all (g5.adjacency.values) shouldBe empty

    val g6 = DiGraph(4 -> "node 1", 5 -> "node 2")(e1,e2)
    g6.nodes shouldBe Set(4,5)
    g6.edges shouldBe Set(e1,e2)
    g6.nodelabels shouldBe Map(4 -> "node 1", 5 -> "node 2")
    g6.edgelabels shouldBe empty
    for ((k,v) <- g6.adjacency) k match {
      case 4 => v shouldBe Map(e1 -> Set(5), e2 -> Set(5))
      case 5 => v shouldBe Map(e1 -> Set(4), e2 -> Set(4))
    }

    val g7 = DiGraph(4 -> "node 1", 5 -> "node 2")(e1 -> 1, e2 -> 2)
    g7.nodes shouldBe Set(4,5)
    g7.edges shouldBe Set(e1,e2)
    g7.nodelabels shouldBe Map(4 -> "node 1", 5 -> "node 2")
    g7.edgelabels shouldBe Map(e1 -> 1, e2 -> 2)
    for ((k,v) <- g7.adjacency) k match {
      case 4 => v shouldBe Map(e1 -> Set(5), e2 -> Set(5))
      case 5 => v shouldBe Map(e1 -> Set(4), e2 -> Set(4))
    }

    val g8 = DiGraph(4,5 -> "node 2")(e1,e2 -> 2)
    g8.nodes shouldBe Set(4,5)
    g8.edges shouldBe Set(e1,e2)
    g8.nodelabels shouldBe Map(5 -> "node 2")
    g8.edgelabels shouldBe Map(e2 -> 2)
    for ((k,v) <- g8.adjacency) k match {
      case 4 => v shouldBe Map(e1 -> Set(5), e2 -> Set(5))
      case 5 => v shouldBe Map(e1 -> Set(4), e2 -> Set(4))
    }
  }

  it should "remove nodes" in {
    val g = new SimpleGraph
    g.addNodes(4,5)
    g.addEdges(e1,e2)
    g -= 4
    g.nodes shouldBe Set(5)
    g.edges shouldBe empty
    g -= 6
    g.nodes shouldBe Set(5)
    g.edges shouldBe empty
    g -= 5
    g.nodes shouldBe empty
    g.edges shouldBe empty
    g += 4
    g(4).label = "a label"
    g.nodelabels shouldBe Map(4 -> "a label")
    g -= 4
    g.nodelabels shouldBe empty
  }

  val e3 = 5 ~> 6 // same as DiEdge(5, 6)

  it should "remove edges" in {
    val g = new SimpleGraph
    g.addNodes(4,5)
    g.addEdges(e1,e2)
    g -= e1
    g.edges shouldBe Set(e2)
    g.nodes shouldBe Set(4,5)
    g -= e3
    g.edges shouldBe Set(e2)
    g.nodes shouldBe Set(4,5)
    g -= e2
    g.edges shouldBe empty
    g.nodes shouldBe Set(4,5)
    g += e1
    g(e1).label = "a label"
    g.edgelabels shouldBe Map(e1 -> "a label")
    g -= e1
    g.edgelabels shouldBe empty
  }

  it should "know the incoming and outgoing edges of its nodes" in {
    val g = new SimpleGraph
    g.addNodes(4,5,6)
    g.addEdges(e1,e2,e3)
    g(4).incoming shouldBe Set(e2)
    g(4).outgoing shouldBe Set(e1)
    g(5).incoming shouldBe Set(e1)
    g(5).outgoing shouldBe Set(e2,e3)
    g(6).incoming shouldBe Set(e3)
    g(6).outgoing shouldBe empty
    g(4).edgesTo(5) shouldBe Set(e1)
    g(4).edgesTo(6) shouldBe empty
    g(5).edgesTo(4) shouldBe Set(e2)
    g(5).edgesTo(6) shouldBe Set(e3)
    g(6).edgesTo(4) shouldBe empty
    g(6).edgesTo(5) shouldBe empty
    // g(4).incomingFrom(5) shouldBe Set(e2) // not implemented
  }

  val e4 = DiEdge(4, 3)

  it should "tell if it is a subgraph of another graph" in {
    val g1 = new SimpleGraph
    val g2 = new SimpleGraph
    g1.addNodes(4,5,6)
    g1.addEdges(e1,e2,e3)
    g2.addNodes(4,5)
    g2 += e1
    assert(g2 subgraphOf g1)
    g2 += e2
    assert(g2 subgraphOf g1)
    g2 += e4
    assert(!(g2 subgraphOf g1))
  }

  it should "construct induced subgraphs" in {
    val g1 = new SimpleGraph
    g1.addNodes(4,5,6)
    g1.addEdges(e1,e2,e3)
    val g2 = g1.inducedSubgraph(4,5)
    g2.nodes shouldBe Set(4,5)
    g2.edges shouldBe Set(e1,e2)
    assert(g2 subgraphOf g1)
    val g3 = g1.inducedSubgraph(5,6)
    g3.nodes shouldBe Set(5,6)
    g3.edges shouldBe Set(e3)
    assert(g3 subgraphOf g1)
  }

  it should "compute its disjoint sets" in {
    val g = new SimpleGraph
    g.addNodes(4,5,6)
    g.addEdges(e1,e3)
    val ps = g.parents
    all (ps.values map (g.findRoot(_,ps))) shouldEqual
      g.findRoot(ps.values.head,ps)
  }

  val e5 = DiEdge(7,8)

  it should "compute its connected components" in {
    val g1 = new SimpleGraph
    g1.addNodes(4,5,6,7,8)
    g1.addEdges(e1,e2,e5)
    val g2 = g1.inducedSubgraph(4,5)
    val g3 = g1.inducedSubgraph(6)
    val g4 = g1.inducedSubgraph(7,8)
    g1.components.toSet shouldBe Set(g2,g3,g4)
    g1 += e3
    val g5 = g1.inducedSubgraph(4,5,6)
    g1.components.toSet shouldBe Set(g4,g5)
  }

  // TODO: Check DiGraph(u1~>u2,u1~>u3,u1~>u3) connectedIso
  // DiGraph(v1~>v1,v1~>v2,v1~>v3) and Arrow(u1->v1,u2->v2,u2->v3,u3->v1)
  // What did I mean by "and Arrow(...)"?

  it should "tell if it is isomorphic to another graph" in {
    val g1 = new SimpleGraph
    val g2 = new SimpleGraph
    g1.addNodes(4,5,6)
    g1.addEdges(e1,e2,e3)
    g2.addNodes(4,5,6)
    g2.addEdges(e1,e2)
    assert(!g1.iso(g2))
    g2 += e3
    assert(g1 iso g2)
    g2 += 0
    assert(!g1.iso(g2))
  }

  type N2 = String
  type E2 = IdDiEdge[Int,N2]
  type MultiGraph = DiGraph[N2,NL,E2,NL]

  val me1 = IdDiEdge(0,"a","b")
  val me2 = IdDiEdge(1,"a","b")

  "A multigraph" should "allow arbitrarily many edges between any two nodes" in {
    val g = new MultiGraph
    g.addNodes("a","b")
    g.addEdges(me1,me2)
    g.edges.size shouldBe 2
  }

  val c1c2 = IdDiEdge(0,"c1","c2")
  val bc1 = IdDiEdge(1,"b","c1")
  val bc2 = IdDiEdge(2,"b","c2")
  val bc3 = IdDiEdge(3,"b","c1")

  it should "tell if it is isomorphic to another graph" in {
    val g1 = DiGraph(1 -> "A")()
    val g2 = DiGraph(2 -> "B")()
    assert(!g1.iso(g2))
    val g3 = DiGraph(3 -> "A")()
    assert(g1 iso g3)
    val g4 = DiGraph(1,2,3,4,5)(1~~>2,3~~>2,4~~>5)
    val g5 = DiGraph(6,7,8,9,0)(7~~>6,8~~>9,0~~>9)
    assert(g4 iso g5)
    val g6 = DiGraph(6,7,8,9,0)(7~~>6,6~~>7,8~~>9,0~~>9)
    assert(!g4.iso(g6))
  }

  val G = DiGraph.withType[N2,NL,E2,EL]

  it should "compute intersections with other graphs" in {
    val g1 = G("b"->"bimotor","c1"->"chain","c2"->"chain")(bc1,c1c2,bc2)
    val g2 = G("b"->"bimotor","c1"->"chain","c2"->"chain")(bc1,c1c2,bc3)
    val pbs = for ((pb,_,_) <- g1.intersections[N2,E2,N2,E2,DiGraph](g2)) yield pb
    pbs.length shouldBe 21
    pbs(0) shouldBe empty
    pbs(1) shouldBe G("(c2,c2)" -> "chain")()
    pbs(2) shouldBe G("(c2,c1)" -> "chain")()
    pbs(3) shouldBe G("(c1,c2)" -> "chain")()
    pbs(4) shouldBe G("(c1,c1)" -> "chain")()
    pbs(5) shouldBe G("(b,b)" -> "bimotor")()
    pbs(6) shouldBe G("(c1,c1)" -> "chain", "(c2,c2)" -> "chain")()
    assert(pbs(7) iso G("(c1,c1)" -> "chain",
      "(c2,c2)" -> "chain")("(c1,c1)" ~~> "(c2,c2)"))
    pbs(8) shouldBe G("(c1,c2)" -> "chain", "(c2,c1)" -> "chain")()
    pbs(9) shouldBe G("(b,b)" -> "bimotor", "(c2,c2)" -> "chain")()
    pbs(10) shouldBe G("(b,b)" -> "bimotor", "(c2,c1)" -> "chain")()
    assert(pbs(11) iso G("(b,b)" -> "bimotor",
      "(c2,c1)" -> "chain")("(b,b)" ~~> "(c2,c1)"))
    pbs(12) shouldBe G("(b,b)" -> "bimotor", "(c1,c2)" -> "chain")()
    pbs(13) shouldBe G("(b,b)" -> "bimotor", "(c1,c1)" -> "chain")()
    assert(pbs(14) iso G("(b,b)" -> "bimotor",
      "(c1,c1)" -> "chain")("(b,b)" ~~> "(c1,c1)"))
    pbs(15) shouldBe G("(b,b)" -> "bimotor", "(c1,c1)" -> "chain",
      "(c2,c2)" -> "chain")()
    assert(pbs(16) iso G("(b,b)" -> "bimotor", "(c1,c1)" ->
      "chain", "(c2,c2)" -> "chain")("(c1,c1)" ~~> "(c2,c2)"))
    assert(pbs(17) iso G("(b,b)" -> "bimotor", "(c1,c1)" ->
      "chain", "(c2,c2)" -> "chain")("(b,b)" ~~> "(c1,c1)"))
    assert(pbs(18) iso G("(b,b)" -> "bimotor", "(c1,c1)" ->
      "chain", "(c2,c2)" -> "chain")("(b,b)" ~~> "(c1,c1)",
        "(c1,c1)" ~~> "(c2,c2)"))
    pbs(19) shouldBe G("(b,b)" -> "bimotor", "(c1,c2)" -> "chain",
      "(c2,c1)" -> "chain")()
    assert(pbs(20) iso G("(b,b)" -> "bimotor", "(c1,c2)" ->
      "chain", "(c2,c1)" -> "chain")("(b,b)" ~~> "(c2,c1)"))
  }

  it should "compute unions with other graphs" in {
    val g1 = G("b"->"bimotor","c1"->"chain","c2"->"chain")(bc1,c1c2,bc2)
    val g2 = G("b"->"bimotor","c1"->"chain","c2"->"chain")(bc1,c1c2,bc3)
    val pos = for ((po,_,_) <- g1.unions[N2,E2,N2,E2,DiGraph](g2)) yield po
    pos.length shouldBe 21
    assert(pos(0) iso G(
      "(b,)" -> "bimotor", "(c1,)" -> "chain", "(c2,)" -> "chain",
      "(,b)" -> "bimotor", "(,c1)" -> "chain", "(,c2)" -> "chain")(
      "(b,)" ~~> "(c1,)", "(b,)" ~~> "(c2,)", "(c1,)" ~~> "(c2,)",
      "(,b)" ~~> "(,c1)", "(,b)" ~~> "(,c1)", "(,c1)" ~~> "(,c2)"))
    assert(pos(1) iso G(
      "(b,)" -> "bimotor", "(c1,)" -> "chain", "(c2,c2)" -> "chain",
      "(,b)" -> "bimotor", "(,c1)" -> "chain")(
      "(b,)" ~~> "(c1,)", "(b,)" ~~> "(c2,c2)", "(c1,)" ~~> "(c2,c2)",
      "(,b)" ~~> "(,c1)", "(,b)" ~~> "(,c1)", "(,c1)" ~~> "(c2,c2)"))
    assert(pos(2) iso G(
      "(b,)" -> "bimotor", "(c1,)" -> "chain", "(c2,c1)" -> "chain",
      "(,b)" -> "bimotor", "(,c2)" -> "chain")(
      "(b,)" ~~> "(c1,)", "(b,)" ~~> "(c2,c1)", "(c1,)" ~~> "(c2,c1)",
      "(,b)" ~~> "(c2,c1)", "(,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(,c2)"))
    assert(pos(3) iso G(
      "(b,)" -> "bimotor", "(c1,c2)" -> "chain", "(c2,)" -> "chain",
      "(,b)" -> "bimotor", "(,c1)" -> "chain")(
      "(b,)" ~~> "(c1,c2)", "(b,)" ~~> "(c2,)", "(c1,c2)" ~~> "(c2,)",
      "(,b)" ~~> "(,c1)", "(,b)" ~~> "(,c1)", "(,c1)" ~~> "(c1,c2)"))
    assert(pos(4) iso G(
      "(b,)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,)" -> "chain",
      "(,b)" -> "bimotor", "(,c2)" -> "chain")(
      "(b,)" ~~> "(c1,c1)", "(b,)" ~~> "(c2,)", "(c1,c1)" ~~> "(c2,)",
      "(,b)" ~~> "(c1,c1)", "(,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(,c2)"))
    assert(pos(5) iso G(
      "(b,b)" -> "bimotor", "(c1,)" -> "chain", "(c2,)" -> "chain",
      "(,c1)" -> "chain", "(,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,)", "(b,b)" ~~> "(c2,)", "(c1,)" ~~> "(c2,)",
      "(b,b)" ~~> "(,c1)", "(b,b)" ~~> "(,c1)", "(,c1)" ~~> "(,c2)"))
    assert(pos(6) iso G(
      "(b,)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain",
      "(,b)" -> "bimotor")(
      "(b,)" ~~> "(c1,c1)", "(b,)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(,b)" ~~> "(c1,c1)", "(,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(c2,c2)"))
    assert(pos(7) iso G(
      "(b,)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain",
      "(,b)" -> "bimotor")(
      "(b,)" ~~> "(c1,c1)", "(b,)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(,b)" ~~> "(c1,c1)", "(,b)" ~~> "(c1,c1)"))
    assert(pos(8) iso G(
      "(b,)" -> "bimotor", "(c1,c2)" -> "chain", "(c2,c1)" -> "chain",
      "(,b)" -> "bimotor")(
      "(b,)" ~~> "(c1,c2)", "(b,)" ~~> "(c2,c1)", "(c1,c2)" ~~> "(c2,c1)",
      "(,b)" ~~> "(c2,c1)", "(,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(c1,c2)"))
    assert(pos(9) iso G(
      "(b,b)" -> "bimotor", "(c1,)" -> "chain", "(c2,c2)" -> "chain",
      "(,c1)" -> "chain")(
      "(b,b)" ~~> "(c1,)", "(b,b)" ~~> "(c2,c2)", "(c1,)" ~~> "(c2,c2)",
      "(b,b)" ~~> "(,c1)", "(b,b)" ~~> "(,c1)", "(,c1)" ~~> "(c2,c2)"))
    assert(pos(10) iso G(
      "(b,b)" -> "bimotor", "(c1,)" -> "chain", "(c2,c1)" -> "chain",
      "(,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,)", "(b,b)" ~~> "(c2,c1)", "(c1,)" ~~> "(c2,c1)",
      "(b,b)" ~~> "(c2,c1)", "(b,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(,c2)"))
    assert(pos(11) iso G(
      "(b,b)" -> "bimotor", "(c1,)" -> "chain", "(c2,c1)" -> "chain",
      "(,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,)", "(b,b)" ~~> "(c2,c1)", "(c1,)" ~~> "(c2,c1)",
      "(b,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(,c2)"))
    assert(pos(12) iso G(
      "(b,b)" -> "bimotor", "(c1,c2)" -> "chain", "(c2,)" -> "chain",
      "(,c1)" -> "chain")(
      "(b,b)" ~~> "(c1,c2)", "(b,b)" ~~> "(c2,)", "(c1,c2)" ~~> "(c2,)",
      "(b,b)" ~~> "(,c1)", "(b,b)" ~~> "(,c1)", "(,c1)" ~~> "(c1,c2)"))
    assert(pos(13) iso G(
      "(b,b)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,)" -> "chain",
      "(,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c2,)", "(c1,c1)" ~~> "(c2,)",
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(,c2)"))
    assert(pos(14) iso G(
      "(b,b)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,)" -> "chain",
      "(,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c2,)", "(c1,c1)" ~~> "(c2,)",
      "(b,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(,c2)"))
    assert(pos(15) iso G(
      "(b,b)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(c2,c2)"))
    assert(pos(16) iso G(
      "(b,b)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c1,c1)"))
    assert(pos(17) iso G(
      "(b,b)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(b,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(c2,c2)"))
    assert(pos(18) iso G(
      "(b,b)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(b,b)" ~~> "(c1,c1)"))
    assert(pos(19) iso G(
      "(b,b)" -> "bimotor", "(c1,c2)" -> "chain", "(c2,c1)" -> "chain")(
      "(b,b)" ~~> "(c1,c2)", "(b,b)" ~~> "(c2,c1)", "(c1,c2)" ~~> "(c2,c1)",
      "(b,b)" ~~> "(c2,c1)", "(b,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(c1,c2)"))
    assert(pos(20) iso G(
      "(b,b)" -> "bimotor", "(c1,c2)" -> "chain", "(c2,c1)" -> "chain")(
      "(b,b)" ~~> "(c1,c2)", "(b,b)" ~~> "(c2,c1)", "(c1,c2)" ~~> "(c2,c1)",
      "(b,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(c1,c2)"))
    // TODO: another example: glueing a graph with itself and check
    // arrows (very important!)
    val g3 = G("u"->"A","v"->"A")("u"~~>"v")
    val unions = g3.unions[N2,E2,N2,E2,DiGraph](g3.copy)
    unions.length shouldBe 8
  }
}

