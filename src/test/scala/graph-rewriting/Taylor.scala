package hz.ricardo
package graph_rewriting

import moments._

object TaylorRabbits {
  type N = String
  type E = IdDiEdge[Int,N]
  val G = DiGraph.withType[N,Unit,E,Unit]
  // https://www.scala-lang.org/files/archive/spec/2.13/07-implicits.html
  // the next line shouldn't be necessary according to the spec
  implicit val graphBuilder = DiGraph.empty[N,Unit,E,Unit] _
  def main(args: Array[String]): Unit = {
    val (e1, e2) = ("father"~~>"daughter","mother"~~>"daughter")
    val parents = G("father","mother")()
    val one = G("father","mother","daughter")(e1,e2) // one child
    val sex = Rule(parents, one,
      Map("father"->"father","mother"->"mother"), Map(), "k1")
    val two = G("father","mother","daughter","son")( // two children
      e1,e2,"father"~~>"son","mother"~~>"son")
    val family = Rule(one, two, Map("father"->"father",
      "mother"->"mother","daughter"->"daughter"),
      Map(e1->e1,e2->e2), "k2")
    val f = taylorExpansion(3, parents, List(sex,family), Pn(Mn(two)))
      // splitConnectedComponents[N,Unit,E,Unit,DiGraph] _)
    for (i <- 1 to 3)
      println(s"f($i) = " + f(i))
  }
}

