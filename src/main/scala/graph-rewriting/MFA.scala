package graph_rewriting

import scala.annotation.tailrec
import scala.collection.mutable
import mutable.ArrayBuffer

// class MFA[N,NL,E<:DiEdgeLike[N],EL] extends Equation[N,NL,E,EL] {
class MFA[NL,EL] extends Equation[String,NL,IdDiEdge[Int,String],EL] {

  import Graph._
  type N = String
  type E = IdDiEdge[Int,N]
  type R = Rule[N,NL,E,EL]

  // --- Transformers ---

  val splitConnectedComponents: G => Option[Polynomial] =
    (g: G) => if (g.isConnected) None
              else Some(1.0 * g.components)


  // --- Fragmentation ---

  val mfaMaxIter: Int = 20

  def mfa(rules: Seq[R], observables: Seq[G],
    transformers: (G => Option[Polynomial])*): Eqs =
    mfa(mfaMaxIter, rules, observables, transformers: _*)

  def mfa(maxIter: Int, rules: Seq[R], observables: Seq[G],
    transformers: (G => Option[Polynomial])*): Eqs = {

    val reversedRules = rules.map(r => (r, r.reversed)).toMap
    val seen = mutable.ArrayBuffer.empty[G]

    @tailrec
    def loop(i: Int, obss: Seq[G], eqs: Eqs): Eqs =
      if (i > maxIter) eqs
      else obss match {
        case Seq() => eqs
        case hd +: tl => seen find (iso(hd, _)) match {
          case Some(g) => {
            println(AlgEquation(hd, 1.0 * g))
            if (hd == g) loop(i, tl, eqs)
            else loop(i, tl, eqs :+ AlgEquation(hd, 1.0 * g))
          }
          case None => {
            val ps: Seq[Polynomial] = transformers flatMap (f => f(hd))
            require(ps.length <= 1, "two or more possible transformations of " + hd)
            if (ps.length == 1) {
              // add algebraic equation provided by the transformation
              val p = ps.head
              val eq = AlgEquation(hd, p.simplify)
              println(eq)
              seen += hd
              loop(i, tl ++ p.graphs, eqs :+ eq)
            } else {
              // no transformation is aplicable to hd
              val p = Polynomial((for (r <- rules) yield {
                val ropp: Rule[N,NL,E,EL] = reversedRules(r)
                // minimal glueings with the left-hand side
                val deletions: Seq[Monomial] =
                  for ((mg, _, _) <- unions(hd, r.lhs)) yield -r.rate * mg
                // minimal glueings with the right-hand side
                val additions: Seq[Monomial] =
                  for ((mg, _, m) <- unions(hd, ropp.lhs)) yield {
                    ropp(m)
                    r.rate * mg
                  }
                deletions ++ additions
              }).flatten.toVector).simplify
              println(ODE(hd, p))
              seen += hd
              loop(i+1, tl ++ p.graphs, eqs :+ ODE(hd, p))
            }
          }
        }
      }

    loop(0, observables, Vector())
  }
}

