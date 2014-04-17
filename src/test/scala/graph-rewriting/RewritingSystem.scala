package graph_rewriting

import graph_rewriting._
import org.scalatest.FlatSpec

class RewritingSystemSpec extends RewritingSystem with FlatSpec {

  "Inside a rewriting system it" should
  "be possible to create edges and pattern match on them" in {
    def outer = ("A" ~+> "B")(5)
    outer match {
      case n1 :~> n2 + label => ()
    }
  }

  "A graph" should "allow multi-edges" in {
    val g = Graph(outer, outer, outer)
    g.toString  should be "Graph(A, B, A~>B, A~>B, A~>B)"
    g.graphSize should be 3

    g.edges.head.edge match {
      case n1 :~> n2 + label =>
        s"$n1 ~+> $n2 '$label" should be "A ~+> B '5"
    }
  }
}

