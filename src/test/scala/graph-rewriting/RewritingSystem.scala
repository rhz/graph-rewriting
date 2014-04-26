package graph_rewriting

import graph_rewriting._
import org.scalatest.{FlatSpec, Matchers}
// import Matchers._

// class RewritingSystemSpec extends RewritingSystem with FlatSpec {
object RewritingSystemSpec extends FlatSpec with Matchers {

  import RewritingSystem._

  "In a rewriting system" must
  "be possible to create edges and pattern match on them" in {
    val outer = ("A" ~+> "B")("L1")
    outer match {
      case n1 :~> (n2, label) => {
        n1 should be (Node("A", ""))
        n2 should be (Node("B", ""))
        label should be ("L1")
      }
    }
  }

  val outer = ("A" ~+> "B")("L1")

  "A graph" must "allow multi-edges" in {
    val g = Graph(outer, outer, outer)
    g.toString should be ("""Graph("A", "B", ("A"~+>"B")(""), """ +
      """("A"~+>"B")(""), ("A"~+>"B")(""))""")
    g.edges.length should be (3)
    for (e <- g.edges) (e =~= outer) should be (true)
    g.edges.head.edge match {
      case n1 :~> (n2, label) => {
        n1 should be (Node("A", ""))
        n2 should be (Node("B", ""))
        label should be ("L1")
      }
    }
  }

  val b = "b:bimotor"
  val c1 = "c1:chain"
  val c2 = "c2:chain"
  val g1 = Graph(b~>c1, b~>c2, c1~>c2)
  val g2 = Graph(b~>c1, b~>c1, c1~>c2)

  val c1c1 = Node("c1,c1", "chain")
  val c1c2 = Node("c1,c2", "chain")
  val c2c1 = Node("c2,c1", "chain")
  val c2c2 = Node("c2,c2", "chain")
  val bb = Node("b,b", "bimotor")

  "Two graphs" should "intersect" in {
    val pbs = for ((pb, _, _) <- intersections(g1, g2)) yield pb
    pbs.length should be (21)
    pbs(0)  should be (Graph[Node,EqDiEdge]())
    pbs(1)  should be (Graph[Node,EqDiEdge](c2c2))
    pbs(2)  should be (Graph[Node,EqDiEdge](c2c1))
    pbs(3)  should be (Graph[Node,EqDiEdge](c1c2))
    pbs(4)  should be (Graph[Node,EqDiEdge](c1c1))
    pbs(5)  should be (Graph[Node,EqDiEdge](bb))
    pbs(6)  should be (Graph[Node,EqDiEdge](c1c1, c2c2))
    (pbs(7) =~= Graph(c1c1~>c2c2)) should be (true)
    pbs(8)  should be (Graph[Node,EqDiEdge](c1c2, c2c1))
    pbs(9)  should be (Graph[Node,EqDiEdge](bb, c2c2))
    pbs(10) should be (Graph[Node,EqDiEdge](bb, c2c1))
    (pbs(11) =~= Graph(bb~>c2c1)) should be (true)
    pbs(12) should be (Graph[Node,EqDiEdge](bb, c1c2))
    pbs(13) should be (Graph[Node,EqDiEdge](bb, c1c1))
    (pbs(14) =~= Graph(bb~>c1c1)) should be (true)
    // NOTE: There's something fishy here because removing the c2c2
    // node from the next line doesn't make the test fail
    pbs(15) should be (Graph[Node,EqDiEdge](bb, c1c1, c2c2))
    (pbs(16) =~= Graph(bb, c1c1~>c2c2)) should be (true)
    (pbs(17) =~= Graph(c2c2, bb~>c1c1)) should be (true)
    (pbs(18) =~= Graph(bb~>c1c1, c1c1~>c2c2)) should be (true)
    pbs(19) should be (Graph[Node,EqDiEdge](bb, c1c2, c2c1))
    (pbs(20) =~= Graph(c1c2, bb~>c2c1)) should be (true)
  }

  val b_ = Node("b,", "bimotor")
  val _b = Node("b,", "bimotor")
  val c1_ = Node("c1,", "chain")
  val _c1 = Node(",c1", "chain")
  val c2_ = Node("c2,", "chain")
  val _c2 = Node(",c2", "chain")

  "Two graphs" should "intersect" in {
    val pos = for ((po, _, _) <- intersections(g1, g2)) yield po
    pos.length should be (21)
  }

  // TODO: Finish tests for unions
}

