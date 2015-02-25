package graph_rewriting

import scala.annotation.tailrec
import implicits._

object meanfield {

  // --- Transformers ---

  def splitConnectedComponents[N,NL,E<:DiEdgeLike[N],EL](
    g: Graph[N,NL,E,EL]): Option[Mn[N,NL,E,EL]] =
    if (g.isConnected) None else Some(Mn(g.components))


  // --- Fragmentation ---

  val mfaMaxIter: Int = 20

  type N = String
  type E = IdDiEdge[Int, N]

  def mfa[NL,EL](
    rules: Traversable[Rule[N,NL,E,EL]],
    observables: Seq[Graph[N,NL,E,EL]],
    transformers: (Graph[N,NL,E,EL] => Option[Mn[N,NL,E,EL]])*)
      : Vector[Eq[N,NL,E,EL]] =
    mfa(mfaMaxIter, rules, observables, transformers:_*)

  def mfa[NL,EL](maxIter: Int,
    rules: Traversable[Rule[N,NL,E,EL]],
    observables: Seq[Graph[N,NL,E,EL]],
    transformers: (Graph[N,NL,E,EL] => Option[Mn[N,NL,E,EL]])*)
      : Vector[Eq[N,NL,E,EL]] = {

    val reversedRules = rules.map(r => (r, r.reversed())).toMap
    val ti = transformers.zipWithIndex

    @tailrec
    def loop(i: Int, obss: Seq[Graph[N,NL,E,EL]],
      eqs: Vector[Eq[N,NL,E,EL]]): Vector[Eq[N,NL,E,EL]] =
      obss match {
        case Seq() => eqs
        case hd +: tl => eqs find (eq => Graph.iso(hd, eq.lhs)) match {
          case Some(eq) => {
            if (hd == eq.lhs) loop(i, tl, eqs)
            else loop(i, tl, eqs :+ AlgEq(hd, Mn(eq.lhs)))
          }
          case None => {
            val mi = for ((t, i) <- ti; m <- t(hd)) yield (m, i)
            if (mi.length > 1)
              println("more than one transformation (" +
                mi.map(_._2).mkString(",") + ") found for " + hd)
            if (mi.nonEmpty) {
              // add algebraic equation provided by the transformation
              val m = mi.head._1
              val eq = AlgEq(hd, m)
              loop(i, tl ++ m.graphs, eqs :+ eq)
            } else if (i < maxIter) { // create an ode only if i < maxIter
              // no transformation is aplicable to hd
              val p = Pn((for (r <- rules) yield {
                val ropp: Rule[N,NL,E,EL] = reversedRules(r)
                // minimal glueings with the left-hand side
                val deletions: Seq[Mn[N,NL,E,EL]] =
                  for ((mg, _, _) <- Graph.unions(hd, r.lhs))
                  yield (-r.rate * mg)
                // minimal glueings with the right-hand side
                val additions: Seq[Mn[N,NL,E,EL]] =
                  for ((mg, _, m) <- Graph.unions(hd, ropp.lhs);
                       rmg = mg.copy; (comatch, _, _) = ropp(m);
                       lmg = mg.copy; _ = r(comatch)
                       // TODO: relevance test
                       // derivability test
                       if Graph.iso(mg, rmg))
                  yield (r.rate * lmg)
                deletions ++ additions
              // simplifying here can save us some work later
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

