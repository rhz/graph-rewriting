package hz.ricardo
package graph_rewriting

import scala.annotation.tailrec
import scala.language.higherKinds  // TODO: necessary?
import scala.collection.mutable

object moments {

  // --- Transformers ---

  /** Transforms a disconnected graph observable `[A+B+...+C]` into
    * the graph monomial `[A]*[B]*...*[C]`.
    * If graph is connected, returns None.
    */
  def splitConnectedComponents[N, NL, E <: DiEdgeLike[N], EL,
    G[X, Y, Z <: DiEdgeLike[X], W] <: BaseDiGraph[X, Y, Z, W] {
      type This = G[X, Y, Z, W]
    }](g: G[N, NL, E, EL]): Option[Pn[N,NL,E,EL,G]] =
    if (g.isConnected) None else Some(Pn(Mn(g.components)))

  def splitConnectedComponentsUsingMG[N, NL, E <: DiEdgeLike[N], EL,
    G[X, Y, Z <: DiEdgeLike[X], W] <: BaseDiGraph[X, Y, Z, W] {
      type This = G[X, Y, Z, W]
    }](g: G[N, NL, E, EL])(implicit
      nodeUnifier: Unifier[N, N, N],
      edgeUnifier: (G[N, NL, E, EL], Map[N, N], Map[N, N]) => Unifier[E, E, E],
      graphBuilder: () => G[N, NL, E, EL])
      : Option[Pn[N,NL,E,EL,G]] =
    if (g.isConnected) None else {
      val gs = g.components
      // QUESTION: How do we minimally glue 3 or more graphs?
      if (gs.size != 2) None else {
        val Seq(g1,g2) = gs.toSeq
        Some(Pn(for ((g,_,_) <- g1.unions[N, E, N, E, G](g2).tail) yield
          Mn(g)) - (Mn(g1) * g2))
      }
    }

  def transformIfIso[N, NL, E <: DiEdgeLike[N], EL,
    G[X, Y, Z <: DiEdgeLike[X], W] <: BaseDiGraph[X, Y, Z, W]](
    gs: Traversable[G[N, NL, E, EL]],
    result: Pn[N, NL, E, EL, G])
      : G[N, NL, E, EL] => Option[Pn[N, NL, E, EL, G]] =
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
  def generateMeanODEs[N, NL, E <: DiEdgeLike[N], EL,
    G[X, Y, Z <: DiEdgeLike[X], W] <: BaseDiGraph[X, Y, Z, W] {
      type This = G[X, Y, Z, W]
    }](
    maxNumODEs: Int,
    rules: Traversable[Rule[N, NL, E, EL, G]],
    observables: Seq[G[N, NL, E, EL]],
    transformers: (G[N, NL, E, EL] => Option[Pn[N, NL, E, EL, G]])*)(implicit
      nodeUnifier: Unifier[N, N, N],
      edgeUnifier: (G[N, NL, E, EL], Map[N, N], Map[N, N]) => Unifier[E, E, E],
      graphBuilder: () => G[N, NL, E, EL])
      : Vector[Eq[N, NL, E, EL, G]] = {

    val ti = transformers.zipWithIndex

    @tailrec
    def loop(i: Int, obss: Seq[G[N, NL, E, EL]],
      eqs: Vector[Eq[N, NL, E, EL, G]]): Vector[Eq[N, NL, E, EL, G]] =
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
                val deletions: Seq[Mn[N, NL, E, EL, G]] =
                  for (mg <- hd.leftUnions(r)) yield (-r.rate * mg)
                // minimal glueings with the right-hand side
                val additions: Seq[Mn[N, NL, E, EL, G]] =
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

  def taylorExpansion[N, NL, E <: DiEdgeLike[N], EL,
    G[X, Y, Z <: DiEdgeLike[X], W] <: BaseDiGraph[X, Y, Z, W] {
      type This = G[X, Y, Z, W] }](
    maxDegree: Int,
    initialGraph: G[N, NL, E, EL],
    rules: Traversable[Rule[N, NL, E, EL, G]],
    observable: Pn[N, NL, E, EL, G],
    transformers: (G[N, NL, E, EL] => Option[Pn[N, NL, E, EL, G]])*)(implicit
      nodeUnifier: Unifier[N, N, N],
      edgeUnifier: (G[N, NL, E, EL], Map[N, N], Map[N, N]) => Unifier[E, E, E],
      graphBuilder: () => G[N, NL, E, EL])
      : (Double => BigDecimal) = {

    val eqs = mutable.ArrayBuffer.empty[Eq[N, NL, E, EL, G]]
    def fragment(g: G[N, NL, E, EL])
        : (Boolean, Eq[N, NL, E, EL, G]) =
      eqs find (eq => g iso eq.lhs) match {
        case Some(eq) => (false, eq)
        case None =>
          (true, (for (t <- transformers; p <- t(g)) yield p) match {
            case p +: _ => AlgEq(g,p)
            case _ => ODE(g, Pn((for (r <- rules) yield {
              // minimal glueings with the left-hand side
              val deletions: Seq[Mn[N, NL, E, EL, G]] =
                for (mg <- g.leftUnions(r)) yield (-r.rate * mg)
              // minimal glueings with the right-hand side
              val additions: Seq[Mn[N, NL, E, EL, G]] =
                for (mg <- g.rightUnions(r)) yield (r.rate * mg)
              deletions ++ additions
              // simplifying here can save us some work later
            }).flatten.toVector).simplify)
          })
      }

    def expand(obs: Pn[N, NL, E, EL, G]): Pn[N, NL, E, EL, G] =
      (for (m <- obs.terms) yield m match {
        case Mn(c, Vector(g), Vector()) => {
          val (isNew,eq) = fragment(g)
          if (isNew) eqs += eq
          c * (eq match {
            case AlgEq(_,rhs) => expand(rhs)
            case ODE(_,rhs) => rhs
          })
        }
        case _ => throw new IllegalArgumentException(
          s"polynomial $obs is not a linear combination: " +
          s"the guilty monomial is $m")
      }).foldLeft(Pn.zero[N,NL,E,EL,G])(_+_).simplify

    val qi = (1 to maxDegree).foldLeft(Vector(observable))({
      case (qi,i) => expand(qi.head) +: qi })

    val numInstances = mutable.Map.empty[G[N, NL, E, EL], Int]
    def count(g: G[N, NL, E, EL]): Int =
      numInstances.get(g) match {
        case Some(n) => n
        case None => {
          val n = g.arrowsTo(initialGraph).size
          numInstances(g) = n
          n
        }
      }

    def prod(gs: Vector[G[N, NL, E, EL]]): BigInt =
      gs.map(count).product

    def evalRatePn(rp: RatePn): BigDecimal =
      (for (RateMn(c,n,d) <- rp.terms) yield
        c * n.map(_.value).product / d.map(_.value).product).sum

    def computeTaylorCoef(q: Pn[N, NL, E, EL, G]): BigDecimal =
      (for (Mn(c,n,d) <- q.terms) yield
        evalRatePn(c) * BigDecimal(prod(n)) / BigDecimal(prod(d))).sum

    case class Acc(tn: BigDecimal, nfac: BigInt, sum: BigDecimal)

    val taylorCoefs: Array[BigDecimal] = qi.map(computeTaylorCoef).toArray
    val factorials: Array[BigDecimal] = (2 to (maxDegree+1)).scanLeft(
      BigDecimal(1))(_*_).toArray

    (t => (0 to maxDegree).foldLeft((BigDecimal(1), BigDecimal(0)))({
      case ((tn,sum), i) => (tn*t,
        sum + (taylorCoefs(i) * tn / factorials(i)))
    })._2)
  }
}

