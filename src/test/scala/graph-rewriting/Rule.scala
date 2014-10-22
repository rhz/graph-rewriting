package graph_rewriting

import org.scalatest.{FlatSpec, Matchers}
import scala.collection.{mutable => m}
import implicits._

class RuleSpec extends FlatSpec with Matchers {

  def G[N,NL](nodes: (N,NL)*)(edges: IdDiEdge[Int,N]*) =
    Graph[N,NL,IdDiEdge[Int,N],String](
      nodes map (_._1), nodes, edges, List())

  val cnt = utils.Counter()
  implicit class IdDiEdgeConst[N](n1: N) {
    def ~~> (n2: N) = IdDiEdge(cnt(), n1, n2)
  }

  // -- Nodes --

  "An AddNode action" should "apply to a match" in {
    val lhs = G(1 -> "A")()
    val rhs = G(1 -> "A", 2 -> "A")()
    val action = AddNode(lhs, rhs, Map(1 -> 1), Map(), 2)
    val mix = G(1 -> "A", 2 -> "B")(1 ~~> 2)
    val m = Arrow(lhs, mix, Map(1 -> 1), Map())
    val (comatch, modNodes, modEdges) = action(m)
    mix.nodes shouldBe Set(1, 2, 3)
    mix(3).label shouldBe Some("A")
    comatch.dom shouldBe rhs
    comatch.cod shouldBe mix
    comatch.n shouldBe Map(1 -> 1, 2 -> 3)
    comatch.e shouldBe empty
    modNodes shouldBe Set(3)
    modEdges shouldBe empty
  }

  it should "be reversible" in {
    val lhs = G(1 -> "A")()
    val rhs = G(1 -> "A", 2 -> "A")()
    val action = AddNode(lhs, rhs, Map(1 -> 2), Map(), 1)
    val inv = action.reversed
    inv shouldBe a [DelNode[_,_,_,_]]
    inv.dom shouldBe rhs
    inv.cod shouldBe lhs
    inv.n shouldBe Map(2 -> 1)
    inv.e shouldBe empty
    inv.nodeLhs shouldBe 1
  }


  "An DelNode action" should "apply to a match" in {
    val lhs = G(1 -> "A", 2 -> "A")()
    val rhs = G(1 -> "A")()
    val action = DelNode(lhs, rhs, Map(1 -> 1), Map(), 2)
    val (e1, e2) = (3 ~~> 2, 2 ~~> 3)
    val mix = G(1 -> "A", 2 -> "B", 3 -> "A")(e1, e2)
    val m = Arrow(lhs, mix, Map(1 -> 1, 2 -> 3), Map())
    val (comatch, modNodes, modEdges) = action(m)
    mix.nodes shouldBe Set(1, 2)
    mix.edges shouldBe empty
    comatch.dom shouldBe rhs
    comatch.cod shouldBe mix
    comatch.n shouldBe Map(1 -> 1)
    comatch.e shouldBe empty
    modNodes shouldBe Set(3)
    modEdges shouldBe Set(e1, e2)
  }

  it should "be reversible" in {
    val rhs = G(1 -> "A", 2 -> "A")()
    val lhs = G(1 -> "A")()
    val action = DelNode(lhs, rhs, Map(2 -> 1), Map(), 1)
    val inv = action.reversed
    inv shouldBe a [AddNode[_,_,_,_]]
    inv.dom shouldBe rhs
    inv.cod shouldBe lhs
    inv.n shouldBe Map(1 -> 2)
    inv.e shouldBe empty
    inv.nodeRhs shouldBe 1
  }


  "An SetNodeLabel action" should "apply to a match" in {
    val edgeLhs = 1 ~~> 2
    val edgeRhs = 1 ~~> 2
    val lhs = G(1 -> "A", 2 -> "A")(edgeLhs)
    val rhs = G(1 -> "B", 2 -> "A")(edgeRhs)
    // The crossing in the node map makes everything too complicated
    // I made it so to check that the comatch is produced correctly
    // by mapping the match through the action's node map.
    val action = SetNodeLabel(lhs, rhs, Map(1 -> 2, 2 -> 1),
      Map(edgeLhs -> edgeRhs), 2)
    val edgeMix = 1 ~~> 2
    val mix = G(1 -> "A", 2 -> "A", 3 -> "B")(edgeMix)
    val m = Arrow(lhs, mix, Map(1 -> 1, 2 -> 2), Map(edgeLhs -> edgeMix))
    val (comatch, modNodes, modEdges) = action(m)
    mix.nodes shouldBe Set(1, 2, 3)
    mix.edges shouldBe Set(edgeMix)
    mix(1).label shouldBe Some("A")
    mix(2).label shouldBe Some("B")
    mix(3).label shouldBe Some("B")
    comatch.dom shouldBe rhs
    comatch.cod shouldBe mix
    comatch.n shouldBe Map(2 -> 1, 1 -> 2)
    comatch.e shouldBe Map(edgeRhs -> edgeMix)
    modNodes shouldBe Set(2)
    modEdges shouldBe empty
  }

  it should "be reversible" in {
    val edgeLhs = 1 ~~> 2
    val edgeRhs = 1 ~~> 2
    val lhs = G(1 -> "A", 2 -> "A")(edgeLhs)
    val rhs = G(1 -> "B", 2 -> "A")(edgeRhs)
    val action = SetNodeLabel(lhs, rhs, Map(1 -> 1, 2 -> 2),
      Map(edgeLhs -> edgeRhs), 1)
    val inv = action.reversed
    inv shouldBe a [SetNodeLabel[_,_,_,_]]
    inv.dom shouldBe rhs
    inv.cod shouldBe lhs
    inv.n shouldBe Map(1 -> 1, 2 -> 2)
    inv.e shouldBe Map(edgeRhs -> edgeLhs)
    inv.nodeLhs shouldBe 1
  }


  // -- Edges --

  "An AddEdge action" should "apply to a match" in {
    val edgeRhs = 1 ~~> 2
    val lhs = G(1 -> "A", 2 -> "B")()
    val rhs = G(1 -> "A", 2 -> "B")(edgeRhs)
    val action = AddEdge(lhs, rhs, Map(1 -> 1, 2 -> 2), Map(), edgeRhs)
    val mix = G(1 -> "A", 2 -> "B")()
    val m = Arrow(lhs, mix, Map(1 -> 1, 2 -> 2), Map())
    val (comatch, modNodes, modEdges) = action(m)
    val edgeMix = IdDiEdge(0, 1, 2)
    mix.nodes shouldBe Set(1, 2)
    mix.edges shouldBe Set(edgeMix)
    comatch.dom shouldBe rhs
    comatch.cod shouldBe mix
    comatch.n shouldBe Map(1 -> 1, 2 -> 2)
    comatch.e shouldBe Map(edgeRhs -> edgeMix)
    modNodes shouldBe Set(1, 2)
    modEdges shouldBe Set(edgeMix)
  }

  it should "be reversible" in {
    val edgeRhs = 1 ~~> 2
    val lhs = G(1 -> "A", 2 -> "B")()
    val rhs = G(1 -> "A", 2 -> "B")(edgeRhs)
    val action = AddEdge(lhs, rhs, Map(1 -> 1, 2 -> 2), Map(), edgeRhs)
    val inv = action.reversed
    inv shouldBe a [DelEdge[_,_,_,_]]
    inv.dom shouldBe rhs
    inv.cod shouldBe lhs
    inv.n shouldBe Map(1 -> 1, 2 -> 2)
    inv.e shouldBe empty
    inv.edgeLhs shouldBe edgeRhs
  }


  "An DelEdge action" should "apply to a match" in {
    val edgeLhs = 1 ~~> 2
    val lhs = G(1 -> "A", 2 -> "B")(edgeLhs)
    val rhs = G(1 -> "A", 2 -> "B")()
    val action = DelEdge(lhs, rhs, Map(1 -> 1, 2 -> 2), Map(), edgeLhs)
    val (e1, e2) = (1 ~~> 2, 2 ~~> 1)
    val mix = G(1 -> "A", 2 -> "B")(e1, e2)
    val m = Arrow(lhs, mix, Map(1 -> 1, 2 -> 2), Map(edgeLhs -> e1))
    val (comatch, modNodes, modEdges) = action(m)
    mix.nodes shouldBe Set(1, 2)
    mix.edges shouldBe Set(e2)
    comatch.dom shouldBe rhs
    comatch.cod shouldBe mix
    comatch.n shouldBe Map(1 -> 1, 2 -> 2)
    comatch.e shouldBe empty
    modNodes shouldBe empty
    modEdges shouldBe Set(e1)
  }

  it should "be reversible" in {
    val edgeLhs = 1 ~~> 2
    val lhs = G(1 -> "A", 2 -> "B")(edgeLhs)
    val rhs = G(1 -> "A", 2 -> "B")()
    val action = DelEdge(lhs, rhs, Map(1 -> 1, 2 -> 2), Map(), edgeLhs)
    val inv = action.reversed
    inv shouldBe a [AddEdge[_,_,_,_]]
    inv.dom shouldBe rhs
    inv.cod shouldBe lhs
    inv.n shouldBe Map(1 -> 1, 2 -> 2)
    inv.e shouldBe empty
    inv.edgeRhs shouldBe edgeLhs
  }


  "An SetEdgeLabel action" should "apply to a match" in {
    val edgeLhs = 1 ~~> 2
    val edgeRhs = 1 ~~> 2
    val lhs = G(1 -> "A", 2 -> "A")(edgeLhs)
    val rhs = G(1 -> "A", 2 -> "A")(edgeRhs)
    rhs(edgeRhs).label = "a label"
    val action = SetEdgeLabel(lhs, rhs, Map(1 -> 1, 2 -> 2),
      Map(edgeLhs -> edgeRhs), edgeLhs)
    val (e1, e2) = (1 ~~> 2, 2 ~~> 1)
    val mix = G(1 -> "A", 2 -> "A")(e1, e2)
    val m = Arrow(lhs, mix, Map(1 -> 1, 2 -> 2), Map(edgeLhs -> e1))
    val (comatch, modNodes, modEdges) = action(m)
    mix.nodes shouldBe Set(1, 2)
    mix.edges shouldBe Set(e1, e2)
    mix(e1).label shouldBe Some("a label")
    mix(e2).label shouldBe None
    comatch.dom shouldBe rhs
    comatch.cod shouldBe mix
    comatch.n shouldBe Map(1 -> 1, 2 -> 2)
    comatch.e shouldBe Map(edgeRhs -> e1)
    modNodes shouldBe empty
    modEdges shouldBe Set(e1)
  }

  it should "be reversible" in {
    val edgeLhs = 1 ~~> 2
    val edgeRhs = 1 ~~> 2
    val lhs = G(1 -> "A", 2 -> "A")(edgeLhs)
    val rhs = G(1 -> "A", 2 -> "A")(edgeRhs)
    rhs(edgeRhs).label = "a label"
    val action = SetEdgeLabel(lhs, rhs, Map(1 -> 1, 2 -> 2),
      Map(edgeLhs -> edgeRhs), edgeLhs)
    val inv = action.reversed
    inv shouldBe a [SetEdgeLabel[_,_,_,_]]
    inv.dom shouldBe rhs
    inv.cod shouldBe lhs
    inv.n shouldBe Map(1 -> 1, 2 -> 2)
    inv.e shouldBe Map(edgeRhs -> edgeLhs)
    inv.edgeLhs shouldBe edgeRhs
  }


  // -- Rules --

  "A rule" should "compute its atomic actions" in {
    // add node
    val l1 = G(1 -> "A")()
    val r1 = G(1 -> "A", 2 -> "A")()
    Rule(l1, r1, Map(1 -> 1), Map()).actions shouldBe Seq(
      AddNode(l1, r1, Map(1 -> 1), Map(), 2))
    // del node
    val l2 = G(1 -> "A", 2 -> "A")()
    val r2 = G(1 -> "A")()
    Rule(l2, r2, Map(1 -> 1), Map()).actions shouldBe Seq(
      DelNode(l2, r2, Map(1 -> 1), Map(), 2))
    // set node
    val e1 = 1 ~~> 2
    val l3 = G(1 -> "A", 2 -> "A")(e1)
    val r3 = G(1 -> "B", 2 -> "A")(e1)
    Rule(l3, r3, Map(1 -> 1, 2 -> 2), Map(e1 -> e1)).actions shouldBe
      Seq(SetNodeLabel(l3, r3, Map(1 -> 1, 2 -> 2), Map(e1 -> e1), 1))
    // add edge
    val l4 = G(1 -> "A", 2 -> "B")()
    val r4 = G(1 -> "A", 2 -> "B")(e1)
    Rule(l4, r4, Map(1 -> 1, 2 -> 2), Map()).actions shouldBe Seq(
      AddEdge(l4, r4, Map(1 -> 1, 2 -> 2), Map(), e1))
    // del edge
    val l5 = G(1 -> "A", 2 -> "B")(e1)
    val r5 = G(1 -> "A", 2 -> "B")()
    Rule(l5, r5, Map(1 -> 1, 2 -> 2), Map()).actions shouldBe Seq(
      DelEdge(l5, r5, Map(1 -> 1, 2 -> 2), Map(), e1))
    // set edge
    val l6 = G(1 -> "A", 2 -> "A")(e1)
    val r6 = G(1 -> "A", 2 -> "A")(e1)
    r6(e1).label = "a label"
    Rule(l6, r6, Map(1 -> 1, 2 -> 2), Map(e1 -> e1)).actions shouldBe
      Seq(SetEdgeLabel(l6, r6, Map(1 -> 1, 2 -> 2), Map(e1 -> e1), e1))
    // all of them
    val e2 = 2 ~~> 1
    val e3 = 1 ~~> 2
    val l7 = G(1 -> "A", 2 -> "A", 0 -> "A")(e1, e3)
    val r7 = G(1 -> "B", 2 -> "A", 3 -> "A")(e2, e3)
    l7(e3).label = "label 1"
    r7(e3).label = "label 2"
    Rule(l7, r7, Map(1 -> 1, 2 -> 2), Map(e3 -> e3)).actions shouldBe
      Seq(AddNode(l7, r7, Map(1 -> 1, 2 -> 2), Map(e3 -> e3), 3),
          DelNode(l7, r7, Map(1 -> 1, 2 -> 2), Map(e3 -> e3), 0),
          SetNodeLabel(l7, r7, Map(1 -> 1, 2 -> 2), Map(e3 -> e3), 1),
          AddEdge(l7, r7, Map(1 -> 1, 2 -> 2), Map(e3 -> e3), e2),
          DelEdge(l7, r7, Map(1 -> 1, 2 -> 2), Map(e3 -> e3), e1),
          SetEdgeLabel(l7, r7, Map(1 -> 1, 2 -> 2), Map(e3 -> e3), e3))
  }

  it should "apply to a match" in {
    val e1 = 1 ~~> 2
    val e2 = 2 ~~> 1
    val e3 = 1 ~~> 2
    val lhs = G(1 -> "A", 2 -> "A", 0 -> "A")(e1, e3)
    val rhs = G(1 -> "B", 2 -> "A", 3 -> "A")(e2, e3)
    lhs(e3).label = "label 1"
    rhs(e3).label = "label 2"
    val r = Rule(lhs, rhs, Map(1 -> 1, 2 -> 2), Map(e3 -> e3))
    val mix = G(0 -> "A", 1 -> "A", 2 -> "A", 3 -> "A")(e1, e3)
    val m = Arrow(lhs, mix, Map(0 -> 0, 1 -> 1, 2 -> 2),
      Map(e1 -> e1, e3 -> e3))
    val (comatch, modNodes, modEdges) = r(m)
    mix.nodes shouldBe Set(1, 2, 3, 4)
    mix.nodelabels shouldBe Map(1 -> "B", 2 -> "A", 3 -> "A", 4 -> "A")
    val e4 = IdDiEdge(0, 2, 1)
    mix.edges shouldBe Set(e3, e4)
    mix.edgelabels shouldBe Map(e3 -> "label 2")
    comatch.dom shouldBe rhs
    comatch.cod shouldBe mix
    comatch.n shouldBe Map(1 -> 1, 2 -> 2, 3 -> 4)
    comatch.e shouldBe Map(e3 -> e3, e2 -> e4)
    modNodes shouldBe Set(0, 1, 2, 4)
    modEdges shouldBe Set(e1, e3, e4)
  }

  it should "be reversible" in {
    val e1 = 1 ~~> 2
    val e2 = 2 ~~> 1
    val e3 = 1 ~~> 2
    val lhs = G(1 -> "A", 2 -> "A", 0 -> "A")(e1, e3)
    val rhs = G(1 -> "B", 2 -> "A", 3 -> "A")(e2, e3)
    lhs(e3).label = "label 1"
    rhs(e3).label = "label 2"
    val r = Rule(lhs, rhs, Map(1 -> 1, 2 -> 2), Map(e3 -> e3))
    val inv = r.reversed
    inv shouldBe a [Rule[_,_,_,_]]
    inv.dom shouldBe rhs
    inv.cod shouldBe lhs
    inv.n shouldBe Map(1 -> 1, 2 -> 2)
    inv.e shouldBe Map(e3 -> e3)
  }

  // By "apply reversibly" I mean: apply the rule and then its inverse
  // to a match, the second comatch is isomorphic to the original
  // match and the final mixture is isomorphic to the original one.
  it should "apply reversibly if match is derivable" in {
    val e1 = 1 ~~> 2
    val e2 = 2 ~~> 1
    val e3 = 1 ~~> 2
    val lhs = G(1 -> "A", 2 -> "A", 0 -> "A")(e1, e3)
    val rhs = G(1 -> "B", 2 -> "A", 3 -> "A")(e2, e3)
    lhs(e3).label = "label 1"
    rhs(e3).label = "label 2"
    val r = Rule(lhs, rhs, Map(1 -> 1, 2 -> 2), Map(e3 -> e3))
    val mix = G(0 -> "A", 1 -> "A", 2 -> "A", 3 -> "A")(e1, e3)
    val copy = mix.copy
    val m = Arrow(lhs, mix, Map(0 -> 0, 1 -> 1, 2 -> 2),
      Map(e1 -> e1, e3 -> e3))
    val (comatch, _, _) = r(m)
    val (m2, _, _) = r.reversed(comatch)
    m.dom shouldBe m2.dom
    m.cod shouldBe m2.cod
    // TODO: How do we test for isomorphic matches?
    // m.n shouldBe m2.n
    // m.e shouldBe m2.e
    assert(Graph.iso(copy, m2.cod))
  }

  it should "not apply reversibly if match is not derivable" in {
    // del node
    val lhs = G(1 -> "A")()
    val rhs = G[Int,String]()()
    val r = Rule(lhs, rhs, Map(), Map())
    val mix = G(1 -> "A", 2 -> "A")(1 ~~> 2)
    val copy = mix.copy
    val m = Arrow(lhs, mix, Map(1 -> 1), Map())
    val (comatch, _, _) = r(m)
    val (m2, _, _) = r.reversed(comatch)
    assert(!Graph.iso(copy, m2.cod))
    /*
    // TODO: Should this be the case?
    // set edge
    val e = 1 ~~> 2
    val lhs = G(1 -> "A", 2 -> "A")(e)
    val rhs = G(1 -> "A", 2 -> "A")(e)
    rhs(e).label = "a label"
    val r = Rule(lhs, rhs, Map(1 -> 1, 2 -> 2), Map(e -> e))
    val mix = G(1 -> "A", 2 -> "A")(e)
    val copy = mix.copy
    val m = Arrow(lhs, mix, Map(1 -> 1, 2 -> 2), Map(e -> e))
    val (comatch, _, _) = r(m)
    val (m2, _, _) = r.reversed(comatch)
    println(s"copy = $copy")
    println(s"m2.cod = ${m2.cod}")
    println(s"m2.cod.edgelabels = ${m2.cod.edgelabels}")
    assert(!Graph.iso(copy, m2.cod))
    */
  }
}

