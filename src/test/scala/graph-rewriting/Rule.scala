package graph_rewriting

import org.scalatest.{FlatSpec, Matchers}
import scala.collection.{mutable => m}

class RuleSpec extends FlatSpec with Matchers {

  type G = Graph[String, String, IdDiEdge[Int,String], String]

  def G(nodes: (String, String)*)(edges: IdDiEdge[Int,String]*) =
    Graph[String, String, IdDiEdge[Int,String], String](
      nodes map (_._1), nodes, edges, List())

  val cnt = utils.Counter()
  implicit class IdDiEdgeConst[N](n1: N) {
    def ~~> (n2: N) = IdDiEdge(cnt(), n1, n2)
  }

  // "A rule" should "be constructible" in {
  // }
}

