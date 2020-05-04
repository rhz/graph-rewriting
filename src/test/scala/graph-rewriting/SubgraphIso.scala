package hz.ricardo
package graph_rewriting

import moments._
import org.scalameter.api._

object SugraphIsoBenchmark extends PerformanceTest.Quickbenchmark {

  val numNodes: Gen[Int] = Gen.range("numNodes")(10,100,10)

  type N = Int
  type E = IdDiEdge[Int,N]
  val G = DiGraph.withType[N,Unit,E,Unit]

  val g = G(0,1,2)(0~~>1,0~~>2)
  var hs = for (i <- numNodes) yield
    (i, G(0 to i, for (j <- 1 to i) yield (0~~>j)))

  performance of "DiGraph" in {
    measure method "arrowsTo" in {
      using(hs) in { case (i,h) =>
        assert(g.arrowsTo(h).length == i*(i-1))
      }
    }
  }
}

