package hz.ricardo
package graph_rewriting

import scala.collection.mutable
import moments._

object KochSnowflake {
  // N should be Int but there's no NodeUnifier for Int yet
  type N = String
  type E = IdDiEdge[Int,N]
  type NL = Int
  type EL = Unit
  val G = DiGraph.withType[N,NL,E,EL]
  // https://www.scala-lang.org/files/archive/spec/2.13/07-implicits.html
  // the next line shouldn't be necessary according to the spec
  implicit val graphBuilder = DiGraph.empty[N,NL,E,EL] _
  def e(x: N): E = IdDiEdge[Int,N](0, "?1", x)
  def main(args: Array[String]): Unit = {

    val g0 = G("?1", "0"->0, "?2")(e("0"), "0"~~>"?2")
    val g1 = G("?1", "1"->1, "?2")(e("1"), "1"~~>"?2")
    val g2 = G("?1", "2"->2, "?2")(e("2"), "2"~~>"?2")
    val g3 = G("?1", "3"->3, "?2")(e("3"), "3"~~>"?2")
    val g4 = G("?1", "4"->4, "?2")(e("4"), "4"~~>"?2")
    val g5 = G("?1", "5"->5, "?2")(e("5"), "5"~~>"?2")

    val h0 = G("?1", "-1"->(-1), "0"->0, "1"->1, "5"->5, "6"->0, "-2"->(-2), "?2")(
      e("-1"), "-1"~~>"0", "0"~~>"1", "1"~~>"5", "5"~~>"6", "6"~~>"-2", "-2"~~>"?2")
    val h1 = G("?1", "-1"->(-1), "1"->1, "2"->2, "0"->0, "7"->1, "-2"->(-2), "?2")(
      e("-1"), "-1"~~>"1", "1"~~>"2", "2"~~>"0", "0"~~>"7", "7"~~>"-2", "-2"~~>"?2")
    val h2 = G("?1", "-1"->(-1), "2"->2, "3"->3, "1"->1, "8"->2, "-2"->(-2), "?2")(
      e("-1"), "-1"~~>"2", "2"~~>"3", "3"~~>"1", "1"~~>"8", "8"~~>"-2", "-2"~~>"?2")
    val h3 = G("?1", "-1"->(-1), "3"->3, "4"->4, "2"->2, "9"->3, "-2"->(-2), "?2")(
      e("-1"), "-1"~~>"3", "3"~~>"4", "4"~~>"2", "2"~~>"9", "9"~~>"-2", "-2"~~>"?2")
    val h4 = G("?1", "-1"->(-1), "4"->4, "5"->5, "3"->3, "10"->4, "-2"->(-2), "?2")(
      e("-1"), "-1"~~>"4", "4"~~>"5", "5"~~>"3", "3"~~>"10", "10"~~>"-2", "-2"~~>"?2")
    val h5 = G("?1", "-1"->(-1), "5"->5, "0"->0, "4"->4, "11"->5, "-2"->(-2), "?2")(
      e("-1"), "-1"~~>"5", "5"~~>"0", "0"~~>"4", "4"~~>"11", "11"~~>"-2", "-2"~~>"?2")

    val r0 = Rule(g0, h0, Map("?1"->"?1", "0"->"0", "?2"->"?2"), Map(), "k0")
    val r1 = Rule(g1, h1, Map("?1"->"?1", "1"->"1", "?2"->"?2"), Map(), "k1")
    val r2 = Rule(g2, h2, Map("?1"->"?1", "2"->"2", "?2"->"?2"), Map(), "k2")
    val r3 = Rule(g3, h3, Map("?1"->"?1", "3"->"3", "?2"->"?2"), Map(), "k3")
    val r4 = Rule(g4, h4, Map("?1"->"?1", "4"->"4", "?2"->"?2"), Map(), "k4")
    val r5 = Rule(g5, h5, Map("?1"->"?1", "5"->"5", "?2"->"?2"), Map(), "k5")

    // observables
    val o1 = G("-1"->(-1), "-3"->(-1), "-5"->(-1))(
      "-1"~~>"-3", "-3"~~>"-5")
    val o2 = G("-2"->(-2), "-4"->(-2), "-6"->(-2))(
      "-2"~~>"-4", "-4"~~>"-6")

    // invariants in string rewriting systems:
    // * linearity
    // * acyclicity
    // def linearity(g: DiGraph[N,NL,E,EL]): Option[Pn[N,NL,E,EL,DiGraph]] =
    //   if (g.nodes forall (n => (g(n).inDegree == 1) && (g(n).outDegree == 1))) None
    //   else Some(Pn.zero)
    def invariants(g: DiGraph[N,NL,E,EL]): Option[Pn[N,NL,E,EL,DiGraph]] =
      if (!g.isConnected) None
      else {
        val xs = g.nodes filter (g(_).inDegree == 0)
        val visited = mutable.Set.empty[N]
        def linearAndAcyclic(y: N): Boolean = {
          visited += y
          val ys = g(y).outgoing
          if (ys.isEmpty) true
          else if (ys.size == 1) {
            val z = ys.head.target
            if (visited contains z) false // cyclic
            else linearAndAcyclic(z)
          } else false // non-linear
        } // youtube: squarepusher tundra
        if (xs.size == 1 && linearAndAcyclic(xs.head)) None
        else Some(Pn.zero)
      }

    def char(l: NL): String =
      if (l == -1) "<" else if (l == -2) ">" else l.toString

    def words(g: DiGraph[N,NL,E,EL]): String =
      if (!g.isConnected)
        (for (h <- g.components) yield words(h)).mkString(" + ")
      else {
        def word(y: N): String = {
          val ys = g(y).outgoing
          g.nodelabels.mapValues(char _).getOrElse(y, "?") ++
          (if (ys.nonEmpty) word(ys.head.target) else "")
        }
        val xs = g.nodes.filter(g(_).inDegree == 0)
        require(xs.size == 1, s"not a word: $g")
        word(xs.head)
      }

    // for (mg <- o1.rightUnions(r0)) println(mg)
    // val r0r = r0.reversed
    // for ((mg, _, m) <- o1.unions[N,E,N,E,DiGraph](r0r.lhs)) {
    //   if (invariants(mg) == None) {
    //     println("before:")
    //     println(words(g))
    //   }
    //   println(mg)
    //   r0r(m)
    //   if (invariants(mg) == None) {
    //     println("after:")
    //     println(words(g))
    //   }
    //   println()
    // }
    val odes = generateMeanODEs[N,NL,E,EL,DiGraph](10,
      List(r0), //, r1, r2, r3, r4, r5),
      List(o1), //, o2),
      invariants _)
    val p = ODEPrinter(odes)
    val names = new IncrementalNaming[N,NL,E,EL,DiGraph]()
    p.print(names)
    println()
    for ((g,n) <- names.seq if invariants(g) == None)
      println(s"$n := ${words(g)}")
    // p.saveAsOctave("pa.m", 5.0, 1000,
    //   g => if (g eq g1) 1.0 else 0.0)
  }
}

