package graph_rewriting

import org.scalatest.{FlatSpec, Matchers}
import scala.collection.{mutable => m}

class GraphSpec extends FlatSpec with Matchers {

  type SimpleGraph = Graph[Int, String, DiEdge[Int], String]

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
    g.nodes shouldBe Set(0, 1)
    g.edges shouldBe empty
    g += 0
    g.nodes shouldBe Set(0, 1)
    g.edges shouldBe empty
    g.nodelabels shouldBe empty
    g.edgelabels shouldBe empty
    g.adjacency.keySet shouldBe Set(0, 1)
    all (g.adjacency.values) shouldBe empty
  }

  it should "add nodes in bulk" in {
    val g = new SimpleGraph
    g.nodes shouldBe empty
    g.edges shouldBe empty
    g.addNodes(2, 3)
    g.nodes shouldBe Set(2, 3)
    g.edges shouldBe empty
  }

  val e1 = DiEdge(4, 5)
  val e2 = DiEdge(5, 4)

  it should "add same edge only once" in {
    val g = new SimpleGraph
    g.addNodes(4, 5)
    g += e1
    g.nodes shouldBe Set(4, 5)
    g.edges shouldBe Set(e1)
    g += e2
    g.nodes shouldBe Set(4, 5)
    g.edges shouldBe Set(e1, e2)
    g += e1
    g.nodes shouldBe Set(4, 5)
    g.edges shouldBe Set(e1, e2)
    g.nodelabels shouldBe empty
    g.edgelabels shouldBe empty
    for ((k, v) <- g.adjacency) k match {
      case 4 => v shouldBe Map(e1 -> Set(5), e2 -> Set(5))
      case 5 => v shouldBe Map(e1 -> Set(4), e2 -> Set(4))
    }
  }

  it should "add edges in bulk" in {
    val g = new SimpleGraph
    g.addNodes(4, 5)
    g.addEdges(e1, e2)
    g.nodes shouldBe Set(4, 5)
    g.edges shouldBe Set(e1, e2)
  }

  it should "add labels to nodes" in {
    val g = new SimpleGraph
    g.addNodes(4, 5)
    g.addEdges(e1, e2)
    g(4).label shouldBe None
    g(5).label shouldBe None

    g(4).label = "node 4"
    g(4).label shouldBe Some("node 4")
    g(5).label shouldBe None

    g(5).label = "node 5"
    g(4).label shouldBe Some("node 4")
    g(5).label shouldBe Some("node 5")

    // adding node labels should not add nodes or edges
    g.nodes shouldBe Set(4, 5)
    g.edges shouldBe Set(e1, e2)
  }

  it should "add labels to edges" in {
    val g = new SimpleGraph
    g.addNodes(4, 5)
    g.addEdges(e1, e2)
    g(e1).label shouldBe None
    g(e2).label shouldBe None

    g(e1).label = "edge 1"
    g(e1).label shouldBe Some("edge 1")
    g(e2).label shouldBe None

    g(e2).label = "edge 2"
    g(e1).label shouldBe Some("edge 1")
    g(e2).label shouldBe Some("edge 2")

    // adding edge labels should not add nodes or edges
    g.nodes shouldBe Set(4, 5)
    g.edges shouldBe Set(e1, e2)
  }

  it should "be constructible" in {
    val g0 = Graph[Int, String, DiEdge[Int], String]()()
    g0.nodes shouldBe empty
    g0.edges shouldBe empty
    g0.nodelabels shouldBe empty
    g0.edgelabels shouldBe empty
    g0.adjacency shouldBe empty

    val g1 = Graph[Int, String, DiEdge[Int], String](4, 5)()
    g1.nodes shouldBe Set(4, 5)
    g1.edges shouldBe empty
    g1.nodelabels shouldBe empty
    g1.edgelabels shouldBe empty
    g1.adjacency.keySet shouldBe Set(4, 5)
    all (g1.adjacency.values) shouldBe empty

    val g2 = Graph[Int, String, DiEdge[Int], String](4, 5)(e1, e2)
    g2.nodes shouldBe Set(4, 5)
    g2.edges shouldBe Set(e1, e2)
    g2.nodelabels shouldBe empty
    g2.edgelabels shouldBe empty
    for ((k, v) <- g2.adjacency) k match {
      case 4 => v shouldBe Map(e1 -> Set(5), e2 -> Set(5))
      case 5 => v shouldBe Map(e1 -> Set(4), e2 -> Set(4))
    }

    val g3 = Graph[Int, String, DiEdge[Int], String](
      List(4, 5),
      Map(4 -> "node 4", 5 -> "node 5"),
      List(e1, e2),
      Map(e1 -> "edge 1", e2 -> "edge 2"))
    g3.nodes shouldBe Set(4, 5)
    g3.edges shouldBe Set(e1, e2)
    g3.nodelabels shouldBe Map(4 -> "node 4", 5 -> "node 5")
    g3.edgelabels shouldBe Map(e1 -> "edge 1", e2 -> "edge 2")
    for ((k, v) <- g3.adjacency) k match {
      case 4 => v shouldBe Map(e1 -> Set(5), e2 -> Set(5))
      case 5 => v shouldBe Map(e1 -> Set(4), e2 -> Set(4))
    }
  }

  it should "remove nodes" in {
    val g = new SimpleGraph
    g.addNodes(4, 5)
    g.addEdges(e1, e2)
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
    g -= 4
    g.nodelabels shouldBe empty
  }

  val e3 = DiEdge(5, 6)

  it should "remove edges" in {
    val g = new SimpleGraph
    g.addNodes(4, 5)
    g.addEdges(e1, e2)
    g -= e1
    g.edges shouldBe Set(e2)
    g.nodes shouldBe Set(4, 5)
    g -= e3
    g.edges shouldBe Set(e2)
    g.nodes shouldBe Set(4, 5)
    g -= e2
    g.edges shouldBe empty
    g.nodes shouldBe Set(4, 5)
    g += e1
    g(e1).label = "a label"
    g -= e1
    g.edgelabels shouldBe empty
  }

  it should "know the incoming and outgoing edges of its nodes" in {
    val g = new SimpleGraph
    g.addNodes(4, 5, 6)
    g.addEdges(e1, e2, e3)
    g(4).incoming shouldBe Set(e2)
    g(4).outgoing shouldBe Set(e1)
    g(5).incoming shouldBe Set(e1)
    g(5).outgoing shouldBe Set(e2, e3)
    g(6).incoming shouldBe Set(e3)
    g(6).outgoing shouldBe empty
    g(4).outgoingTo(5) shouldBe Set(e1)
    g(4).outgoingTo(6) shouldBe empty
    g(5).outgoingTo(4) shouldBe Set(e2)
    g(5).outgoingTo(6) shouldBe Set(e3)
    g(6).outgoingTo(4) shouldBe empty
    g(6).outgoingTo(5) shouldBe empty
    // g(4).incomingFrom(5) shouldBe Set(e2) // not implemented
  }

  val e4 = DiEdge(4, 3)

  it should "tell if it is a subgraph of another graph" in {
    val g1 = new SimpleGraph
    val g2 = new SimpleGraph
    g1.addNodes(4, 5, 6)
    g1.addEdges(e1, e2, e3)
    g2.addNodes(4, 5)
    g2 += e1
    assert(g2 subgraphOf g1)
    g2 += e2
    assert(g2 subgraphOf g1)
    g2 += e4
    assert(!(g2 subgraphOf g1))
  }

  it should "construct induced subgraphs" in {
    val g1 = new SimpleGraph
    g1.addNodes(4, 5, 6)
    g1.addEdges(e1, e2, e3)
    val g2 = g1.inducedSubgraph(4, 5)
    g2.nodes shouldBe Set(4, 5)
    g2.edges shouldBe Set(e1, e2)
    assert(g2 subgraphOf g1)
    val g3 = g1.inducedSubgraph(5, 6)
    g3.nodes shouldBe Set(5, 6)
    g3.edges shouldBe Set(e3)
    assert(g3 subgraphOf g1)
  }

  val e5 = DiEdge(7, 8)

  it should "compute its disjoint sets" in {
    val g = new SimpleGraph
    g.addNodes(4, 5, 6)
    g.addEdges(e1, e3)
    val ps = g.parents
    all (ps.values map (g.findRoot(_, ps))) shouldEqual
      g.findRoot(ps.values.head, ps)
  }

  it should "compute its connected components" in {
    val g1 = new SimpleGraph
    g1.addNodes(4, 5, 6, 7, 8)
    g1.addEdges(e1, e2, e5)
    val g2 = g1.inducedSubgraph(4, 5)
    val g3 = g1.inducedSubgraph(6)
    val g4 = g1.inducedSubgraph(7, 8)
    g1.components.toSet shouldBe Set(g2, g3, g4)
    g1 += e3
    val g5 = g1.inducedSubgraph(4, 5, 6)
    g1.components.toSet shouldBe Set(g4, g5)
  }

  it should "tell if it is isomorphic to another graph" in {
    import Graph._
    val g1 = new SimpleGraph
    val g2 = new SimpleGraph
    g1.addNodes(4, 5, 6)
    g1.addEdges(e1, e2, e3)
    g2.addNodes(4, 5, 6)
    g2.addEdges(e1, e2)
    assert(!iso(g1, g2))
    g2 += e3
    assert(iso(g1, g2))
    g2 += 0
    assert(!iso(g1, g2))
  }

  type MultiGraph = Graph[String, String, IdDiEdge[Int,String], String]

  val me1 = IdDiEdge(0, "a", "b")
  val me2 = IdDiEdge(1, "a", "b")

  "A multigraph" should "allow arbitrarily many edges between any two nodes" in {
    val g = new MultiGraph
    g.addNodes("a", "b")
    g.addEdges(me1, me2)
    g.edges.size shouldBe 2
  }

  val c1c2 = IdDiEdge(0, "c1", "c2")
  val bc1 = IdDiEdge(1, "b", "c1")
  val bc2 = IdDiEdge(2, "b", "c2")
  val bc3 = IdDiEdge(3, "b", "c1")

  def G(nodes: (String, String)*)(edges: IdDiEdge[Int,String]*) =
    Graph[String, String, IdDiEdge[Int,String], String](
      nodes map (_._1), nodes, edges, List())

  val cnt = utils.Counter()
  implicit class IdDiEdgeConst[N](n1: N) {
    def ~~> (n2: N) = IdDiEdge(cnt(), n1, n2)
  }

  it should "compute intersections with other graphs" in {
    val g1 = G("b" -> "bimotor", "c1" -> "chain", "c2" -> "chain")(
      bc1, c1c2, bc2)
    val g2 = G("b" -> "bimotor", "c1" -> "chain", "c2" -> "chain")(
      bc1, c1c2, bc3)
    val pbs = for ((pb, _, _) <- Graph.intersections(g1, g2)) yield pb
    pbs.length shouldBe 21
    pbs(0) shouldBe empty
    pbs(1) shouldBe G("(c2,c2)" -> "chain")()
    pbs(2) shouldBe G("(c2,c1)" -> "chain")()
    pbs(3) shouldBe G("(c1,c2)" -> "chain")()
    pbs(4) shouldBe G("(c1,c1)" -> "chain")()
    pbs(5) shouldBe G("(b,b)" -> "bimotor")()
    pbs(6) shouldBe G("(c1,c1)" -> "chain", "(c2,c2)" -> "chain")()
    assert(Graph.iso(pbs(7), G("(c1,c1)" -> "chain",
      "(c2,c2)" -> "chain")("(c1,c1)" ~~> "(c2,c2)")))
    pbs(8) shouldBe G("(c1,c2)" -> "chain", "(c2,c1)" -> "chain")()
    pbs(9) shouldBe G("(b,b)" -> "bimotor", "(c2,c2)" -> "chain")()
    pbs(10) shouldBe G("(b,b)" -> "bimotor", "(c2,c1)" -> "chain")()
    assert(Graph.iso(pbs(11), G("(b,b)" -> "bimotor",
      "(c2,c1)" -> "chain")("(b,b)" ~~> "(c2,c1)")))
    pbs(12) shouldBe G("(b,b)" -> "bimotor", "(c1,c2)" -> "chain")()
    pbs(13) shouldBe G("(b,b)" -> "bimotor", "(c1,c1)" -> "chain")()
    assert(Graph.iso(pbs(14), G("(b,b)" -> "bimotor",
      "(c1,c1)" -> "chain")("(b,b)" ~~> "(c1,c1)")))
    pbs(15) shouldBe G("(b,b)" -> "bimotor", "(c1,c1)" -> "chain",
      "(c2,c2)" -> "chain")()
    assert(Graph.iso(pbs(16), G("(b,b)" -> "bimotor", "(c1,c1)" ->
      "chain", "(c2,c2)" -> "chain")("(c1,c1)" ~~> "(c2,c2)")))
    assert(Graph.iso(pbs(17), G("(b,b)" -> "bimotor", "(c1,c1)" ->
      "chain", "(c2,c2)" -> "chain")("(b,b)" ~~> "(c1,c1)")))
    assert(Graph.iso(pbs(18), G("(b,b)" -> "bimotor", "(c1,c1)" ->
      "chain", "(c2,c2)" -> "chain")("(b,b)" ~~> "(c1,c1)",
        "(c1,c1)" ~~> "(c2,c2)")))
    pbs(19) shouldBe G("(b,b)" -> "bimotor", "(c1,c2)" -> "chain",
      "(c2,c1)" -> "chain")()
    assert(Graph.iso(pbs(20), G("(b,b)" -> "bimotor", "(c1,c2)" ->
      "chain", "(c2,c1)" -> "chain")("(b,b)" ~~> "(c2,c1)")))
  }

  it should "compute unions with other graphs" in {
    val g1 = G("b" -> "bimotor", "c1" -> "chain", "c2" -> "chain")(
      bc1, c1c2, bc2)
    val g2 = G("b" -> "bimotor", "c1" -> "chain", "c2" -> "chain")(
      bc1, c1c2, bc3)
    val pos = for ((po, _, _) <- Graph.unions(g1, g2)) yield po
    pos.length shouldBe 21
    assert(Graph.iso(pos(0), G(
      "(b,)" -> "bimotor", "(c1,)" -> "chain", "(c2,)" -> "chain",
      "(,b)" -> "bimotor", "(,c1)" -> "chain", "(,c2)" -> "chain")(
      "(b,)" ~~> "(c1,)", "(b,)" ~~> "(c2,)", "(c1,)" ~~> "(c2,)",
      "(,b)" ~~> "(,c1)", "(,b)" ~~> "(,c1)", "(,c1)" ~~> "(,c2)")))
    assert(Graph.iso(pos(1), G(
      "(b,)" -> "bimotor", "(c1,)" -> "chain", "(c2,c2)" -> "chain",
      "(,b)" -> "bimotor", "(,c1)" -> "chain")(
      "(b,)" ~~> "(c1,)", "(b,)" ~~> "(c2,c2)", "(c1,)" ~~> "(c2,c2)",
      "(,b)" ~~> "(,c1)", "(,b)" ~~> "(,c1)", "(,c1)" ~~> "(c2,c2)")))
    assert(Graph.iso(pos(2), G(
      "(b,)" -> "bimotor", "(c1,)" -> "chain", "(c2,c1)" -> "chain",
      "(,b)" -> "bimotor", "(,c2)" -> "chain")(
      "(b,)" ~~> "(c1,)", "(b,)" ~~> "(c2,c1)", "(c1,)" ~~> "(c2,c1)",
      "(,b)" ~~> "(c2,c1)", "(,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(,c2)")))
    assert(Graph.iso(pos(3), G(
      "(b,)" -> "bimotor", "(c1,c2)" -> "chain", "(c2,)" -> "chain",
      "(,b)" -> "bimotor", "(,c1)" -> "chain")(
      "(b,)" ~~> "(c1,c2)", "(b,)" ~~> "(c2,)", "(c1,c2)" ~~> "(c2,)",
      "(,b)" ~~> "(,c1)", "(,b)" ~~> "(,c1)", "(,c1)" ~~> "(c1,c2)")))
    assert(Graph.iso(pos(4), G(
      "(b,)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,)" -> "chain",
      "(,b)" -> "bimotor", "(,c2)" -> "chain")(
      "(b,)" ~~> "(c1,c1)", "(b,)" ~~> "(c2,)", "(c1,c1)" ~~> "(c2,)",
      "(,b)" ~~> "(c1,c1)", "(,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(,c2)")))
    assert(Graph.iso(pos(5), G(
      "(b,b)" -> "bimotor", "(c1,)" -> "chain", "(c2,)" -> "chain",
      "(,c1)" -> "chain", "(,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,)", "(b,b)" ~~> "(c2,)", "(c1,)" ~~> "(c2,)",
      "(b,b)" ~~> "(,c1)", "(b,b)" ~~> "(,c1)", "(,c1)" ~~> "(,c2)")))
    assert(Graph.iso(pos(6), G(
      "(b,)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain",
      "(,b)" -> "bimotor")(
      "(b,)" ~~> "(c1,c1)", "(b,)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(,b)" ~~> "(c1,c1)", "(,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(c2,c2)")))
    assert(Graph.iso(pos(7), G(
      "(b,)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain",
      "(,b)" -> "bimotor")(
      "(b,)" ~~> "(c1,c1)", "(b,)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(,b)" ~~> "(c1,c1)", "(,b)" ~~> "(c1,c1)")))
    assert(Graph.iso(pos(8), G(
      "(b,)" -> "bimotor", "(c1,c2)" -> "chain", "(c2,c1)" -> "chain",
      "(,b)" -> "bimotor")(
      "(b,)" ~~> "(c1,c2)", "(b,)" ~~> "(c2,c1)", "(c1,c2)" ~~> "(c2,c1)",
      "(,b)" ~~> "(c2,c1)", "(,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(c1,c2)")))
    assert(Graph.iso(pos(9), G(
      "(b,b)" -> "bimotor", "(c1,)" -> "chain", "(c2,c2)" -> "chain",
      "(,c1)" -> "chain")(
      "(b,b)" ~~> "(c1,)", "(b,b)" ~~> "(c2,c2)", "(c1,)" ~~> "(c2,c2)",
      "(b,b)" ~~> "(,c1)", "(b,b)" ~~> "(,c1)", "(,c1)" ~~> "(c2,c2)")))
    assert(Graph.iso(pos(10), G(
      "(b,b)" -> "bimotor", "(c1,)" -> "chain", "(c2,c1)" -> "chain",
      "(,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,)", "(b,b)" ~~> "(c2,c1)", "(c1,)" ~~> "(c2,c1)",
      "(b,b)" ~~> "(c2,c1)", "(b,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(,c2)")))
    assert(Graph.iso(pos(11), G(
      "(b,b)" -> "bimotor", "(c1,)" -> "chain", "(c2,c1)" -> "chain",
      "(,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,)", "(b,b)" ~~> "(c2,c1)", "(c1,)" ~~> "(c2,c1)",
      "(b,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(,c2)")))
    assert(Graph.iso(pos(12), G(
      "(b,b)" -> "bimotor", "(c1,c2)" -> "chain", "(c2,)" -> "chain",
      "(,c1)" -> "chain")(
      "(b,b)" ~~> "(c1,c2)", "(b,b)" ~~> "(c2,)", "(c1,c2)" ~~> "(c2,)",
      "(b,b)" ~~> "(,c1)", "(b,b)" ~~> "(,c1)", "(,c1)" ~~> "(c1,c2)")))
    assert(Graph.iso(pos(13), G(
      "(b,b)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,)" -> "chain",
      "(,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c2,)", "(c1,c1)" ~~> "(c2,)",
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(,c2)")))
    assert(Graph.iso(pos(14), G(
      "(b,b)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,)" -> "chain",
      "(,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c2,)", "(c1,c1)" ~~> "(c2,)",
      "(b,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(,c2)")))
    assert(Graph.iso(pos(15), G(
      "(b,b)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(c2,c2)")))
    assert(Graph.iso(pos(16), G(
      "(b,b)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c1,c1)")))
    assert(Graph.iso(pos(17), G(
      "(b,b)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(b,b)" ~~> "(c1,c1)", "(c1,c1)" ~~> "(c2,c2)")))
    assert(Graph.iso(pos(18), G(
      "(b,b)" -> "bimotor", "(c1,c1)" -> "chain", "(c2,c2)" -> "chain")(
      "(b,b)" ~~> "(c1,c1)", "(b,b)" ~~> "(c2,c2)", "(c1,c1)" ~~> "(c2,c2)",
      "(b,b)" ~~> "(c1,c1)")))
    assert(Graph.iso(pos(19), G(
      "(b,b)" -> "bimotor", "(c1,c2)" -> "chain", "(c2,c1)" -> "chain")(
      "(b,b)" ~~> "(c1,c2)", "(b,b)" ~~> "(c2,c1)", "(c1,c2)" ~~> "(c2,c1)",
      "(b,b)" ~~> "(c2,c1)", "(b,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(c1,c2)")))
    assert(Graph.iso(pos(20), G(
      "(b,b)" -> "bimotor", "(c1,c2)" -> "chain", "(c2,c1)" -> "chain")(
      "(b,b)" ~~> "(c1,c2)", "(b,b)" ~~> "(c2,c1)", "(c1,c2)" ~~> "(c2,c1)",
      "(b,b)" ~~> "(c2,c1)", "(c2,c1)" ~~> "(c1,c2)")))
  }
}

