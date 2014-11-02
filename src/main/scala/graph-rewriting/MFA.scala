package graph_rewriting

import scala.annotation.tailrec
import scala.collection.mutable
import mutable.ArrayBuffer
import graph_rewriting.{Eq => GenEq}
import implicits._

class MFA[NL,EL] {

  type N = String
  type E = IdDiEdge[Int,N]
  type G = Graph[N,NL,E,EL]
  type R = Rule[N,NL,E,EL]
  type M = Mn[N,NL,E,EL]
  type P = Pn[N,NL,E,EL]
  type Eq = GenEq[N,NL,E,EL]

  // --- Transformers ---

  val splitConnectedComponents: G => Option[P] =
    (g: G) => if (g.isConnected) None
              else Some(Mn(g.components))


  // --- Fragmentation ---

  val mfaMaxIter: Int = 20

  def mfa(rules: Seq[R], observables: Seq[G],
    transformers: (G => Option[P])*): Vector[Eq] =
    mfa(mfaMaxIter, rules, observables, transformers: _*)

  def mfa(maxIter: Int, rules: Seq[R], observables: Seq[G],
    transformers: (G => Option[P])*): Vector[Eq] = {

    val reversedRules = rules.map(r => (r, r.reversed)).toMap
    val ti = transformers.zipWithIndex

    @tailrec
    def loop(i: Int, obss: Seq[G], eqs: Vector[Eq]): Vector[Eq] =
      obss match {
        case Seq() => eqs
        case hd +: tl => eqs find (eq => Graph.iso(hd, eq.lhs)) match {
          case Some(eq) => {
            if (hd == eq.lhs) loop(i, tl, eqs)
            else loop(i, tl, eqs :+ AlgEq(hd, Mn(eq.lhs)))
          }
          case None => {
            val pi = for ((t, i) <- ti; p <- t(hd)) yield (p, i)
            if (pi.length > 1)
              println("more than one transformation (" +
                pi.map(_._2).mkString(",") + ") found for " + hd)
            if (pi.nonEmpty) {
              // add algebraic equation provided by the transformation
              val p = pi.head._1
              // simplifying here can save us some work later
              val eq = AlgEq(hd, p.simplify)
              loop(i, tl ++ p.graphs, eqs :+ eq)
            } else if (i < maxIter) { // create an ode only if i < maxIter
              // no transformation is aplicable to hd
              val p = Pn((for (r <- rules) yield {
                val ropp: R = reversedRules(r)
                // minimal glueings with the left-hand side
                val deletions: Seq[M] =
                  for ((mg, _, _) <- Graph.unions(hd, r.lhs))
                  yield (-r.rate * mg)
                // minimal glueings with the right-hand side
                val additions: Seq[M] =
                  for ((mg, _, m) <- Graph.unions(hd, ropp.lhs);
                       rmg = mg.copy; (comatch, _, _) = ropp(m);
                       lmg = mg.copy; _ = r(comatch)
                       // TODO: relevance test
                       // derivability test
                       if Graph.iso(mg, rmg))
                  yield (r.rate * lmg)
                deletions ++ additions
              }).flatten.toVector).simplify
              loop(i+1, tl ++ p.graphs, eqs :+ ODE(hd, p))
            }
            else loop(i, tl, eqs)
          }
        }
      }

    loop(0, observables, Vector())
  }
}

