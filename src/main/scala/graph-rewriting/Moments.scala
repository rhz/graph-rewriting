package graph_rewriting

import scala.annotation.tailrec
import implicits._

object moments {

  // --- Transformers ---

  /** Transforms a disconnected graph observable `[A+B+...+C]` into
    * the graph monomial `[A]*[B]*...*[C]`.
    * If graph is connected, returns None.
    */
  def splitConnectedComponents[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    g: G[N,NL,E,EL])(implicit ev: g.G[NL,E,EL] =:= G[N,NL,E,EL])
      : Option[Pn[N,NL,E,EL,G]] =
    if (g.isConnected) None else Some(Pn(Mn(g.components map (ev(_)))))

  def splitConnectedComponentsUsingMG[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,G]](
    g: G[N,NL,E,EL])(implicit
      nodeUnifier: Unifier[N,N,N],
      edgeUnifier: (G[N,NL,E,EL],Map[N,N],Map[N,N]) => Unifier[E,E,E],
      graphBuilder: () => G[N,NL,E,EL],
      ev: g.This =:= G[N,NL,E,EL])
      : Option[Pn[N,NL,E,EL,G]] =
    if (g.isConnected) None else {
      val gs = g.components
      // QUESTION: How do we minimally glue 3 or more graphs?
      if (gs.size != 2) None else {
        val Seq(g1,g2) = gs.map(ev(_)).toSeq
        Some(Pn(for ((g,_,_) <- g1.unions[N,E,N,E,G](g2).tail) yield
          Mn(g)) - (Mn(g1)*g2))
      }
    }

  def transformIfIso[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    gs: Traversable[G[N,NL,E,EL]],
    result: Pn[N,NL,E,EL,G])
      : G[N,NL,E,EL] => Option[Pn[N,NL,E,EL,G]] =
    g => if (gs exists (_ iso g)) Some(result) else None

  def transformIfIso[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    gs: Traversable[G[N,NL,E,EL]],
    result: G[N,NL,E,EL])
      : G[N,NL,E,EL] => Option[Pn[N,NL,E,EL,G]] =
    g => if (gs exists (_ iso g)) Some(Pn(Mn(g))) else None

  def cancelIfIso[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    gs: Traversable[G[N,NL,E,EL]])
      : G[N,NL,E,EL] => Option[Pn[N,NL,E,EL,G]] =
    transformIfIso(gs, Pn.zero[N,NL,E,EL,G])


  // --- Fragmentation ---

  /** Discover at most `maxNumODEs` ordinary differential equations
    * for the mean ocurrence count of a given set of graph
    * `observables` and the graph observables they depend on,
    * under the given set of `rules`.
    * Optionally, a set of `transformers` can be provided.
    * These will be applied to each observable and if some graph
    * monomial is returned, the observable will be equated to that
    * monomial and no ODE will be generated for it.
    * When no monomial is returned (i.e. `None`), an ODE will be
    * generated for that observable if the maximum number of ODEs
    * to be generated hasn't been reached (given by `maxNumODEs`).
    * For a transformer example, see `splitConnectedComponents`.
    */
  def generateMeanODEs[N,NL,E<:DiEdgeLike[N],EL,
    H[X,Y,Z<:DiEdgeLike[X],W] <: ConcreteDiGraph[X,Y,Z,W,H]](
    maxNumODEs: Int,
    rules: Traversable[Rule[N,NL,E,EL,H]],
    observables: Seq[H[N,NL,E,EL]],
    transformers: (H[N,NL,E,EL] => Option[Pn[N,NL,E,EL,H]])*)(implicit
      nodeUnifier: Unifier[N,N,N],
      edgeUnifier: (H[N,NL,E,EL],Map[N,N],Map[N,N]) => Unifier[E,E,E],
      graphBuilder: () => H[N,NL,E,EL])
      // ev: H[N,NL,E,EL]#This <:< H[N,NL,E,EL]) // WARNING: This breaks the compiler
      : Vector[Eq[N,NL,E,EL,H]] = {

    val ti = transformers.zipWithIndex

    @tailrec
    def loop(i: Int, obss: Seq[H[N,NL,E,EL]],
      eqs: Vector[Eq[N,NL,E,EL,H]]): Vector[Eq[N,NL,E,EL,H]] =
      obss match {
        case Seq() => eqs
        case hd +: tl => eqs find (eq => hd iso eq.lhs) match {
          case Some(eq) => {
            if (hd == eq.lhs) loop(i,tl,eqs)
            else loop(i, tl, eqs :+ AlgEq(hd,Pn(Mn(eq.lhs))))
          }
          case None => {
            val pi = for ((t,i) <- ti; p <- t(hd)) yield (p,i)
            if (pi.length > 1)
              println("more than one transformation (" +
                pi.map(_._2).mkString(",") + ") found for " + hd)
            if (pi.nonEmpty) {
              // add algebraic equation provided by the transformation
              val p = pi.head._1
              val eq = AlgEq(hd,p)
              loop(i, tl ++ p.graphs, eqs :+ eq)
            } else if (i < maxNumODEs) { // create an ode only if i < maxNumODEs
              // no transformation is aplicable to hd
              val p = Pn((for (r <- rules) yield {
                // minimal glueings with the left-hand side
                val deletions: Seq[Mn[N,NL,E,EL,H]] =
                  for (mg <- hd.leftUnions(r)) yield (-r.rate * mg)
                // minimal glueings with the right-hand side
                val additions: Seq[Mn[N,NL,E,EL,H]] =
                  for (mg <- hd.rightUnions(r)) yield (r.rate * mg)
                deletions ++ additions
              // simplifying here can save us some work later
              }).flatten.toVector).simplify
              loop(i+1, tl ++ p.graphs, eqs :+ ODE(hd,p))
            }
            else loop(i,tl,eqs)
          }
        }
      }

    loop(0, observables, Vector())
  }
}

