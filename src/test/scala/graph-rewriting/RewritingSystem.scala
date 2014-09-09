package graph_rewriting

import graph_rewriting.RewritingSystem._
import org.scalatest.{FlatSpec, Matchers}

class RewritingSystemSpec extends FlatSpec with Matchers {

  "A node" must "be constructable" in {
    val n = Node("a", "A")
    n.name should be ("a")
    n.label should be ("A")
    node("a:A") should equal (n)
  }

  it should "be matchable" in {
    (node("1:A") =~= node("2:A")) should be (true)
    (node("a:A") =~= node("a:B")) should be (false)
  }

  "An edge" must "be constructable" in {
    val a = Node("a", "A")
    val b = Node("b", "B")
    val e1 = EqDiEdge[Node,String](a, b)("L1")
    e1.source should be (a)
    e1.target should be (b)
    e1.label should be ("L1")
    // RHZ: The compiler has problems with this: error during
    // expansion of this match (this is a scalac bug).
    // e1 match {
    //   case n1 :~> n2 + label => {
    //     n1 should be (a)
    //     n2 should be (b)
    //     label should be ("L1")
    //   }
    // }
    val e2 = (Node("a:A") ~+> Node("b:B"))("L1")
    e2.source should be (a)
    e2.target should be (b)
    e2.label should be ("L1")
    val e3 = Node("a:A") ~> Node("b:B")
    e3.source should equal (a)
    e3.target should equal (b)
    e3.label should be ("")
  }

  it should "be matchable" in {
    ((Node("a:A") ~+> Node("b:B"))("L1") =~=
     (Node("a:A") ~+> Node("b:B"))("L1")) should be (true)
    ((Node("a:A") ~+> Node("b:B"))("L1") =~=
     (Node("a:A") ~+> Node("b:B"))("L2")) should be (false)
  }

  val outer = (Node("a") ~+> Node("b"))("L1")

  "A graph" must "allow multi-edges" in {
    val g = Graph(outer, outer, outer)
    g.edges.length should be (3)
    for (e <- g.edges) {
      e.source should be (Node("a"))
      e.target should be (Node("b"))
      e.label should be ("L1")
      (e.toOuter =~= outer) should be (true)
      // Inner edge can be matched
      // RHZ: The compiler has problems with this: error during
      // expansion of this match (this is a scalac bug).
      // (e.edge match {
      //   case n1 :~> n2 + label => (n1, n2, label)
      // }) should be (Node("A", ""), Node("B", ""), "L1")
    }
  }


  // --- Intersections and Unions ---

  type L = String

  val b = Node("b:bimotor")
  val c1 = Node("c1:chain")
  val c2 = Node("c2:chain")
  val g1 = Graph(b~>c1, b~>c2, c1~>c2)
  val g2 = Graph(b~>c1, b~>c1, c1~>c2)

  val c1c1 = Node("(c1,c1)", "chain")
  val c1c2 = Node("(c1,c2)", "chain")
  val c2c1 = Node("(c2,c1)", "chain")
  val c2c2 = Node("(c2,c2)", "chain")
  val bb = Node("(b,b)", "bimotor")

  "Two graphs" should "have intersections" in {
    val pbs = for ((pb, _, _) <- intersections(g1, g2)) yield pb
    pbs.length should be (21)
    pbs(0)  should be (Graph[Node,EqDiEdge]())
    pbs(1)  should be (Graph[Node,EqDiEdge](c2c2))
    pbs(2)  should be (Graph[Node,EqDiEdge](c2c1))
    pbs(3)  should be (Graph[Node,EqDiEdge](c1c2))
    pbs(4)  should be (Graph[Node,EqDiEdge](c1c1))
    pbs(5)  should be (Graph[Node,EqDiEdge](bb))
    pbs(6)  should be (Graph[Node,EqDiEdge](c1c1, c2c2))
    (pbs(7) sameAs Graph(c1c1~>c2c2)) should be (true)
    pbs(8)  should be (Graph[Node,EqDiEdge](c1c2, c2c1))
    pbs(9)  should be (Graph[Node,EqDiEdge](bb, c2c2))
    pbs(10) should be (Graph[Node,EqDiEdge](bb, c2c1))
    (pbs(11) sameAs Graph(bb~>c2c1)) should be (true)
    pbs(12) should be (Graph[Node,EqDiEdge](bb, c1c2))
    pbs(13) should be (Graph[Node,EqDiEdge](bb, c1c1))
    (pbs(14) sameAs Graph(bb~>c1c1)) should be (true)
    pbs(15) should be (Graph[Node,EqDiEdge](bb, c1c1, c2c2))
    (pbs(16) sameAs Graph(bb, c1c1~>c2c2)) should be (true)
    (pbs(17) sameAs Graph(c2c2, bb~>c1c1)) should be (true)
    (pbs(18) sameAs Graph(bb~>c1c1, c1c1~>c2c2)) should be (true)
    pbs(19) should be (Graph[Node,EqDiEdge](bb, c1c2, c2c1))
    (pbs(20) sameAs Graph(c1c2, bb~>c2c1)) should be (true)
  }

  val b_ = Node("(b,)", "bimotor")
  val _b = Node("(,b)", "bimotor")
  val c1_ = Node("(c1,)", "chain")
  val _c1 = Node("(,c1)", "chain")
  val c2_ = Node("(c2,)", "chain")
  val _c2 = Node("(,c2)", "chain")

  it should "have unions" in {
    val pos = for ((po, _, _) <- intersections(g1, g2)) yield po
    pos.length should be (21)
    // (pos(0).isIsoTo[L](Graph[Node,EqDiEdge](b_, c1_, c2_, _b, _c1, _c2, b_ ~> c1_, b_ ~> c2_, c1_ ~> c2_, _b ~> _c1, _b ~> _c1, _c1 ~> _c2))) should be (true)
    // (pos(1).isIsoTo[L](Graph[Node,EqDiEdge](b_, c1_, _b, _c1, c2c2, b_ ~> c1_, b_ ~> c2c2, c1_ ~> c2c2, _b ~>  _c1, _b ~>  _c1, _c1 ~> c2c2))) should be (true)
    // (pos(2).isIsoTo[L](Graph[Node,EqDiEdge](b_, c1_, _b, _c2, c2c1, b_ ~> c1_, b_ ~> c2c1, c1_ ~> c2c1, _b ~> c2c1, _b ~> c2c1, c2c1 ~> _c2))) should be (true)
    // (pos(3).isIsoTo[L](Graph[Node,EqDiEdge](c1c2))) should be (true)
    // (pos(4).isIsoTo[L](Graph[Node,EqDiEdge](c1c1))) should be (true)
    // (pos(5).isIsoTo[L](Graph[Node,EqDiEdge](bb))) should be (true)
    // (pos(6).isIsoTo[L](Graph[Node,EqDiEdge](c1c1, c2c2))) should be (true)
    // (pos(7).isIsoTo[L](Graph(c1c1 ~> c2c2))) should be (true)
    // (pos(8).isIsoTo[L](Graph[Node,EqDiEdge](c1c2, c2c1))) should be (true)
    // (pos(9).isIsoTo[L](Graph[Node,EqDiEdge](bb, c2c2))) should be (true)
    // (pos(10).isIsoTo[L](Graph[Node,EqDiEdge](bb, c2c1))) should be (true)
    // (pos(11).isIsoTo[L](Graph(bb ~> c2c1))) should be (true)
    // (pos(12).isIsoTo[L](Graph[Node,EqDiEdge](bb, c1c2))) should be (true)
    // (pos(13).isIsoTo[L](Graph[Node,EqDiEdge](bb, c1c1))) should be (true)
    // (pos(14).isIsoTo[L](Graph(bb ~> c1c1))) should be (true)
    // (pos(15).isIsoTo[L](Graph[Node,EqDiEdge](bb, c1c1, c2c2))) should be (true)
    // (pos(16).isIsoTo[L](Graph(bb, c1c1 ~> c2c2))) should be (true)
    // (pos(17).isIsoTo[L](Graph(c2c2, bb ~> c1c1))) should be (true)
    // (pos(18).isIsoTo[L](Graph(bb ~> c1c1, c1c1 ~> c2c2))) should be (true)
    // (pos(19).isIsoTo[L](Graph[Node,EqDiEdge](bb, c1c2, c2c1))) should be (true)
    // (pos(20).isIsoTo[L](Graph(c1c2, bb ~> c2c1))) should be (true)
  }

  "SetNodeLabel" should "only set one node label" in {
    // TODO: Maybe add b to g to be sure r(m) doesn't affect that b
    val a = Node("a:A")
    val b = Node("a:B")
    val r = SetNodeLabel(a, b)
    val g = Graph[Node,EqDiEdge](a)
    val m = Match(r.dom, g)(Map(r.dom.get(a) -> g.get(a)), Map())
    r(m)
    g should equal (Graph[Node,EqDiEdge](b))
  }

  "SetEdgeLabel" should "only set one edge label" in {
    // TODO: Maybe add another edge to g
    val a = Node("a:A")
    val b = Node("b:B")
    val e1 = EqDiEdge(a, b)("label 1")
    val e2 = EqDiEdge(a, b)("label 2")
    val r = SetEdgeLabel(e1, e2)
    val g = Graph(e1)
    val m = Match(r.dom, g)((r.dom.nodes, g.nodes).zipped.toMap,
      (r.dom.edges, g.edges).zipped.toMap)
    r(m)
    (g.isIsoTo[L](Graph(e2))) should be (true)
  }

  "DelNode" should "only remove one node" in {
    val a = Node("a:A")
    val b = Node("b:B")
    val r = DelNode(a)
    val g = Graph[Node,EqDiEdge](a, b)
    val m = Match(r.dom, g)(Map(r.dom.get(a) -> g.get(a)), Map())
    r(m)
    g should equal (Graph[Node,EqDiEdge](b))
  }

  "DelEdge" should "only remove one edge" in {
    // TODO: See above
    val a = Node("a:A")
    val b = Node("b:B")
    val e = EqDiEdge(a, b)("")
    val r = DelEdge(e)
    val g = Graph(e)
    val m = Match(r.dom, g)((r.dom.nodes, g.nodes).zipped.toMap,
      (r.dom.edges, g.edges).zipped.toMap)
    r(m)
    g should equal (Graph[Node,EqDiEdge](a, b))
  }

  "AddNode" should "only add one node" in {
    val a = Node("a:A")
    val b = Node("b:B")
    val r = AddNode(b)
    val g = Graph[Node,EqDiEdge](a)
    val m = Match(r.dom, g)(Map(), Map())
    r(m)
    (g.isIsoTo[L](Graph[Node,EqDiEdge](a, b))) should be (true)
  }

  "AddEdge" should "only add one edge" in {
    val a = Node("a:A")
    val b = Node("b:B")
    val e = EqDiEdge(a, b)("label")
    val r = AddEdge(e)
    val g = Graph[Node,EqDiEdge](a, b)
    val m = Match(r.dom, g)((r.dom.nodes, g.nodes).zipped.toMap, Map())
    r(m)
    (g.isIsoTo[L](Graph(e))) should be (true)
  }
}

