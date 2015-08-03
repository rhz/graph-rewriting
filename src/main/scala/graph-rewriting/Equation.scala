package uk.ac.ed.inf
package graph_rewriting

import scala.collection.mutable
import scala.language.higherKinds  // TODO: necessary?
import utils.Counter

// TODO: Division by polynomials (RatePn and Pn) is tough.

case class UnsupportedOperation(msg: String)
    extends IllegalArgumentException(msg)
case class MissingODE(msg: String)
    extends IllegalStateException(msg)

/** Rate monomials. */
case class RateMn(
  val coef: Double,
  val numer: Vector[Rate],
  val denom: Vector[Rate]) {
  // multiplication and division
  def * (k: Rate) = RateMn(coef, numer :+ k, denom)
  def / (k: Rate) = RateMn(coef, numer, denom :+ k)
  def * (rm: RateMn) = RateMn(coef * rm.coef, numer ++ rm.numer, denom ++ rm.denom)
  def / (rm: RateMn) = RateMn(coef / rm.coef, numer ++ rm.denom, denom ++ rm.numer)
  def * (rp: RatePn): RatePn = rp map (_ * this)
  def * [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    g: G[N,NL,E,EL]) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    Mn(RatePn(this), Vector(g), Vector())
  def / [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    g: G[N,NL,E,EL]) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    Mn(RatePn(this), Vector(), Vector(g))
  def * [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    m: Mn[N,NL,E,EL,G]) // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL])
      : Mn[N,NL,E,EL,G] = Mn(this * m.coef, m.numer, m.denom)
  def / [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    m: Mn[N,NL,E,EL,G]) // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL])
      : Mn[N,NL,E,EL,G] = m.coef match {
    case RatePn(Vector(rm)) => Mn(this / rm, m.denom, m.numer)
    case _ => throw new UnsupportedOperation(
      "can't divide by a rate polynomial")
  }
  def * [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    p: Pn[N,NL,E,EL,G])//(implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL])
      : Pn[N,NL,E,EL,G] = p map (_ * this)
  // addition and substraction
  def + (k: Rate) = RatePn(Vector(this,  RateMn(k)))
  def - (k: Rate) = RatePn(Vector(this, -RateMn(k)))
  def + (rm: RateMn) = RatePn(Vector(this,  rm))
  def - (rm: RateMn) = RatePn(Vector(this, -rm))
  def + (rp: RatePn) = RatePn(this +:   rp .terms)
  def - (rp: RatePn) = RatePn(this +: (-rp).terms)
  def + [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    m: Mn[N,NL,E,EL,G]) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    Pn(Mn[N,NL,E,EL,G](RatePn(this)), m)
  def - [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    m: Mn[N,NL,E,EL,G]) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    Pn(Mn[N,NL,E,EL,G](RatePn(this)), -m)
  def + [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    p: Pn[N,NL,E,EL,G]) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    Pn(Mn[N,NL,E,EL,G](RatePn(this)) +: p.terms)
  def - [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    p: Pn[N,NL,E,EL,G]) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    Pn(Mn[N,NL,E,EL,G](RatePn(this)) +: (-p).terms)
  def unary_- = RateMn(-coef, numer, denom)
  // FIXME: There's a bug in this method
  def simplify: RateMn = {
    val (n, d) = numer.foldLeft((Vector.empty[Rate], denom))({
      case ((n, d), kn) => d.foldLeft((n, Vector.empty[Rate]))({
        case ((n, d), kd) => if (kn == kd) (n, d)
                             else (n :+ kn, d :+ kd) // or is it (kn +: n, kd +: d)?
      })
    })
    RateMn(coef, n, d)
  }
  val eps = 1e-16
  def isZero: Boolean = (coef >= -eps) && (coef <= eps)

  override def toString = this match {
    case RateMn(c  , Vector(), Vector()) => c.toString
    case RateMn(1.0, numer   , Vector()) => numer mkString " * "
    case RateMn(c  , numer   , Vector()) =>
      s"$c * "  + numer.mkString(" * ")
    case RateMn(c  , Vector(), denom   ) =>
      s"$c / (" + denom.mkString(" * ") + ")"
    case RateMn(1.0, numer   , denom   ) =>
      (numer mkString " * ") + " / (" + denom.mkString(" * ") + ")"
    case RateMn(c  , numer   , denom   ) =>
      s"$c * " + numer.mkString(" * ") + " / (" + denom.mkString(" * ") + ")"
  }
  // val formatter = new java.text.DecimalFormat("#.###")
  // override def toString = this match {
  //   case RateMn(c  , Vector(), Vector()) => formatter.format(c)
  //   case RateMn(1.0, numer   , Vector()) => numer mkString " * "
  //   case RateMn(c  , numer   , Vector()) =>
  //     s"${formatter.format(c)} * "  + numer.mkString(" * ")
  //   case RateMn(c  , Vector(), denom   ) =>
  //     s"${formatter.format(c)} / (" + denom.mkString(" * ") + ")"
  //   case RateMn(1.0, numer   , denom   ) =>
  //     (numer mkString " * ") + " / (" + denom.mkString(" * ") + ")"
  //   case RateMn(c  , numer   , denom   ) =>
  //     s"${formatter.format(c)} * " + numer.mkString(" * ") + " / (" +
  //     denom.mkString(" * ") + ")"
  // }
}

object RateMn {
  def zero = RateMn(0.0, Vector(), Vector())
  def one = RateMn(1.0, Vector(), Vector())
  def apply(numer: Vector[Rate], denom: Vector[Rate]): RateMn =
    RateMn(1.0, numer, denom)
  def apply(numer: Rate*): RateMn =
    RateMn(1.0, numer.toVector, Vector())
  def apply(n: Double, numer: Rate*): RateMn =
    RateMn(n, numer.toVector, Vector())
}

/** Rate polynomials. */
case class RatePn(terms: Vector[RateMn]) {
  // NOTE: We don't allow polynomials to be empty.
  // What would it mean to be empty?
  require(terms.nonEmpty, "empty polynomial")
  // multiplication and division
  def * (k: Rate) = RatePn(terms map (_ * k))
  def / (k: Rate) = RatePn(terms map (_ / k))
  def * (rm: RateMn) = RatePn(terms map (_ * rm))
  def / (rm: RateMn) = RatePn(terms map (_ / rm))
  def * (rp: RatePn) = RatePn(for (rm1 <- terms; rm2 <- rp.terms)
                              yield rm1 * rm2)
  def * [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    g: G[N,NL,E,EL]) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    Mn(this, Vector(g), Vector())
  def / [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    g: G[N,NL,E,EL]) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    Mn(this, Vector(), Vector(g))
  def * [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    m: Mn[N,NL,E,EL,G]) // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL])
      : Mn[N,NL,E,EL,G] = Mn(this * m.coef, m.numer, m.denom)
  def / [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    m: Mn[N,NL,E,EL,G]) // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL])
      : Mn[N,NL,E,EL,G] = m.coef match {
    case RatePn(Vector(rm)) => Mn(this / rm, m.denom, m.numer)
    case _ => throw new UnsupportedOperation(
      "can't divide by a rate polynomial")
  }
  def * [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    p: Pn[N,NL,E,EL,G]) // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL])
      : Pn[N,NL,E,EL,G] = p map (_ * this)
  // addition and substraction
  def + (k: Rate) = RatePn(terms :+  RateMn(k))
  def - (k: Rate) = RatePn(terms :+ -RateMn(k))
  def + (rm: RateMn) = RatePn(terms :+  rm)
  def - (rm: RateMn) = RatePn(terms :+ -rm)
  def + (rp: RatePn) = RatePn(terms ++   rp .terms)
  def - (rp: RatePn) = RatePn(terms ++ (-rp).terms)
  def + [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    m: Mn[N,NL,E,EL,G]) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    Pn(Mn[N,NL,E,EL,G](this), m)
  def - [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    m: Mn[N,NL,E,EL,G]) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    Pn(Mn[N,NL,E,EL,G](this), -m)
  def + [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    p: Pn[N,NL,E,EL,G]) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    Pn(Mn[N,NL,E,EL,G](this) +: p.terms)
  def - [N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    p: Pn[N,NL,E,EL,G]) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    Pn(Mn[N,NL,E,EL,G](this) +: (-p).terms)
  def unary_- = RatePn(terms map (-_))
  def simplify: RatePn = {
    val rmns = mutable.ArrayBuffer.empty[RateMn]
    for (rm1 <- terms /*map (_.simplify)*/) {
      val RateMn(c1, n1, d1) = rm1
      rmns indexWhere {
        case RateMn(_, n2, d2) => (n1 == n2) && (d1 == d2) // TODO this should compare multisets, not vectors
      } match {
        case -1 => rmns += rm1
        case i => {
          val RateMn(c2, _, _) = rmns(i)
          rmns(i) = RateMn(c1 + c2, n1, d1)
        }
      }
    }
    val nonZero = rmns.filter(!_.isZero)
    if (nonZero.isEmpty) RatePn.zero else RatePn(nonZero.toVector)
  }
  def isZero: Boolean = terms forall (_.isZero)
  def map(f: RateMn => RateMn) = RatePn(terms map f)
  override def toString =
    if (terms.length == 1) s"${terms.head}"
    else "(" + (terms mkString " + ") + ")"
}

object RatePn {
  def apply(t: RateMn, terms: RateMn*): RatePn = RatePn(t +: terms.toVector)
  def one = RatePn(RateMn(1))
  def zero = RatePn(RateMn(0))
  def unapplySeq(rp: RatePn) = Some(rp.terms)
}

/** Graph monomials. */
class Mn[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
  val coef: RatePn,
  val numer: Vector[G[N,NL,E,EL]],
  val denom: Vector[G[N,NL,E,EL]]) { //(
  // implicit val ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) {
  // multiplication and division
  def * (k: Rate) = Mn(coef * k, numer, denom)
  def / (k: Rate) = Mn(coef / k, numer, denom)
  def * (rm: RateMn) = Mn(coef * rm, numer, denom)
  def / (rm: RateMn) = Mn(coef / rm, numer, denom)
  def * (rp: RatePn) = Mn(coef * rp, numer, denom)
  def * (g: G[N,NL,E,EL]) = Mn(coef, numer :+ g, denom)
  def / (g: G[N,NL,E,EL]) = Mn(coef, numer, denom :+ g)
  def * (m: Mn[N,NL,E,EL,G]) =
    Mn(coef * m.coef, numer ++ m.numer, denom ++ m.denom)
  def / (m: Mn[N,NL,E,EL,G]) = m.coef match {
    case RatePn(Vector(rm)) =>
      Mn(coef / rm, numer ++ m.denom, denom ++ m.numer)
    case _ => throw new UnsupportedOperation(
      "can't divide by a rate polynomial")
  }
  def * (p: Pn[N,NL,E,EL,G]): Pn[N,NL,E,EL,G] = p map (_ * this)
  def / (p: Pn[N,NL,E,EL,G]): Pn[N,NL,E,EL,G] = p match {
    case Pn(Vector(m)) => this / m
    case _ => throw new UnsupportedOperation(
      "can't divide by a graph polynomial")
  }
  // addition and substraction
  def + (k: Rate) = Pn(this, Mn[N,NL,E,EL,G]( RateMn(k)))
  def - (k: Rate) = Pn(this, Mn[N,NL,E,EL,G](-RateMn(k)))
  def + (rm: RateMn) = Pn(this, Mn[N,NL,E,EL,G]( rm))
  def - (rm: RateMn) = Pn(this, Mn[N,NL,E,EL,G](-rm))
  def + (rp: RatePn) = Pn(this, Mn[N,NL,E,EL,G]( rp))
  def - (rp: RatePn) = Pn(this, Mn[N,NL,E,EL,G](-rp))
  def + (m: Mn[N,NL,E,EL,G]) = Pn(this,  m)
  def - (m: Mn[N,NL,E,EL,G]) = Pn(this, -m)
  def + (p: Pn[N,NL,E,EL,G]) = Pn(this +:   p .terms)
  def - (p: Pn[N,NL,E,EL,G]) = Pn(this +: (-p).terms)
  def unary_- = Mn(-coef, numer, denom)
  // equality
  override def equals(other: Any): Boolean = other match {
    case that: Mn[_,_,_,_,_] =>
      (that canEqual this) &&
      (coef == that.coef) &&
      (numer == that.numer) &&
      (denom == that.denom)
    case _ => false
  }
  def canEqual(other: Any): Boolean = other match {
    case _: Mn[_,_,_,_,_] => true
    case _ => false
  }
  override def hashCode: Int =
    41 * (41 * (41 + coef.hashCode) + numer.hashCode) + denom.hashCode
  def graphs: Seq[G[N,NL,E,EL]] = numer ++ denom
  def isZero = this == Mn.zero[N,NL,E,EL,G]
  override def toString = s"Mn($coef, $numer, $denom)"
}

object Mn {
  def zero[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]] = //(
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new Mn[N,NL,E,EL,G](RatePn.zero, Vector(), Vector())
  def one[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]] =
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new Mn[N,NL,E,EL,G](RatePn.one, Vector(), Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    rp: RatePn) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new Mn[N,NL,E,EL,G](rp, Vector(), Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    numer: G[N,NL,E,EL]*) =
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new Mn[N,NL,E,EL,G](RatePn.one, numer.toVector, Vector())
  // TODO: Check that when a Vector of Gs is passed, this function
  // is called and not the one for Traversables.
  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    numer: Vector[G[N,NL,E,EL]]) =
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new Mn[N,NL,E,EL,G](RatePn.one, numer, Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    numer: Traversable[G[N,NL,E,EL]]) =
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new Mn[N,NL,E,EL,G](RatePn.one, numer.toVector, Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    rp: RatePn, numer: G[N,NL,E,EL]*) =
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new Mn[N,NL,E,EL,G](rp, numer.toVector, Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    rp: RatePn, numer: Vector[G[N,NL,E,EL]]) =
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new Mn[N,NL,E,EL,G](rp, numer, Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    rp: RatePn, numer: Traversable[G[N,NL,E,EL]]) =
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new Mn[N,NL,E,EL,G](rp, numer.toVector, Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    rp: RatePn,
    numer: Vector[G[N,NL,E,EL]],
    denom: Vector[G[N,NL,E,EL]]) =
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new Mn[N,NL,E,EL,G](rp, numer, denom)
  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    rp: RatePn,
    numer: Traversable[G[N,NL,E,EL]],
    denom: Traversable[G[N,NL,E,EL]]) =
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new Mn[N,NL,E,EL,G](rp, numer.toVector, denom.toVector)
  def unapply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    m: Mn[N,NL,E,EL,G]) = // (implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    Some(m.coef, m.numer, m.denom)

  // TODO: Pair approximation
  // def pairApproximation[N,NL,E<:DiEdgeLike[N],EL,G[X,Y,Z<:DiEdgeLike[X],W]](
  //   g: G[N,NL,E,EL], intersection: (Set[N], Set[E])): Mn[N,NL,E,EL,G]

  // TODO: Approximate master equation... What is this exactly?
}


/** Graph polynomials. */
class Pn[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
  val terms: Vector[Mn[N,NL,E,EL,G]]) { //(
  // implicit val ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) {
  require(terms.nonEmpty, "empty polynomial")
  // multiplication and division
  def * (k: Rate): Pn[N,NL,E,EL,G] = Pn(terms map (_ * k))
  def / (k: Rate): Pn[N,NL,E,EL,G] = Pn(terms map (_ / k))
  def * (rm: RateMn): Pn[N,NL,E,EL,G] = Pn(terms map (_ * rm))
  def / (rm: RateMn): Pn[N,NL,E,EL,G] = Pn(terms map (_ / rm))
  def * (rp: RatePn): Pn[N,NL,E,EL,G] = Pn(terms map (_ * rp))
  def * (g: G[N,NL,E,EL]): Pn[N,NL,E,EL,G] = Pn(terms map (_ * g))
  def / (g: G[N,NL,E,EL]): Pn[N,NL,E,EL,G] = Pn(terms map (_ / g))
  def * (m: Mn[N,NL,E,EL,G]): Pn[N,NL,E,EL,G] = map(_ * m)
  def / (m: Mn[N,NL,E,EL,G]): Pn[N,NL,E,EL,G] = map(_ / m)
  def * (p: Pn[N,NL,E,EL,G]): Pn[N,NL,E,EL,G] =
    Pn(for (m1 <- terms; m2 <- p.terms) yield m1 * m2)
  def / (p: Pn[N,NL,E,EL,G]): Pn[N,NL,E,EL,G] = p match {
    case Pn(Vector(m)) => map(_ / m)
    case _ => throw new UnsupportedOperation(
      "can't divide by a graph polynomial")
  }
  // addition and substraction
  def + (k: Rate) = Pn(terms :+ Mn[N,NL,E,EL,G]( RateMn(k)))
  def - (k: Rate) = Pn(terms :+ Mn[N,NL,E,EL,G](-RateMn(k)))
  def + (rm: RateMn) = Pn(terms :+ Mn[N,NL,E,EL,G]( rm))
  def - (rm: RateMn) = Pn(terms :+ Mn[N,NL,E,EL,G](-rm))
  def + (rp: RatePn) = Pn(terms :+ Mn[N,NL,E,EL,G]( rp))
  def - (rp: RatePn) = Pn(terms :+ Mn[N,NL,E,EL,G](-rp))
  def + (m: Mn[N,NL,E,EL,G]) = Pn[N,NL,E,EL,G](terms :+  m)
  def - (m: Mn[N,NL,E,EL,G]) = Pn[N,NL,E,EL,G](terms :+ -m)
  def + (p: Pn[N,NL,E,EL,G]) = Pn[N,NL,E,EL,G](terms ++   p .terms)
  def - (p: Pn[N,NL,E,EL,G]) = Pn[N,NL,E,EL,G](terms ++ (-p).terms)
  def unary_- = Pn[N,NL,E,EL,G](terms map (-_))
  // equality
  override def equals(other: Any): Boolean = other match {
    case that: Pn[_,_,_,_,_] =>
      (that canEqual this) && terms == that.terms
    case _ => false
  }
  def canEqual(other: Any): Boolean = other match {
    case _: Pn[_,_,_,_,_] => true
    case _ => false
  }
  override def hashCode: Int = terms.hashCode

  // -- Seq methods --
  def isEmpty = terms.isEmpty
  def nonEmpty = terms.nonEmpty
  def map(f: Mn[N,NL,E,EL,G] => Mn[N,NL,E,EL,G]) = Pn(terms map f)

  // -- Pn methods --
  def isZero: Boolean = this == Pn.zero[N,NL,E,EL,G]
  def graphs: Seq[G[N,NL,E,EL]] = terms flatMap (_.graphs)
  def simplify: Pn[N,NL,E,EL,G] = {
    import DiGraph.isos
    val mns = mutable.ArrayBuffer.empty[Mn[N,NL,E,EL,G]]
    for (m1 <- terms) {
      val Mn(c1, n1, d1) = m1
      mns indexWhere {
        case Mn(_, n2, d2) => isos(n1, n2) && isos(d1, d2)
      } match {
        case -1 => mns += m1
        case i => {
          val Mn(c2, n2, d2) = mns(i)
          mns(i) = Mn(c1 + c2, n2, d2)
        }
      }
    }
    val nonZero = for (m <- mns; c = m.coef.simplify; if !c.isZero)
                  yield Mn(c, m.numer, m.denom)
    if (nonZero.isEmpty) Pn.zero else Pn(nonZero.toVector)
  }

  override def toString = s"Pn($terms)"
}

object Pn {
  def zero[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]] =
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new Pn[N,NL,E,EL,G](Vector(Mn.zero[N,NL,E,EL,G]))
  def one[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]] =
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new Pn[N,NL,E,EL,G](Vector(Mn.one[N,NL,E,EL,G]))
  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    terms: Mn[N,NL,E,EL,G]*) =
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    if (terms.isEmpty) Pn.one[N,NL,E,EL,G]
    else new Pn[N,NL,E,EL,G](terms.toVector)
  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    terms: Traversable[Mn[N,NL,E,EL,G]]) =
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    if (terms.isEmpty) Pn.one[N,NL,E,EL,G]
    else new Pn[N,NL,E,EL,G](terms.toVector)
  def unapply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    p: Pn[N,NL,E,EL,G]) = Some(p.terms)
    // implicit ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) = Some(p.terms)
}

sealed abstract class Eq[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]] { //(
  // implicit val ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) {
  val lhs: G[N,NL,E,EL]
  val rhs: Pn[N,NL,E,EL,G]
}
case class AlgEq[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
  lhs: G[N,NL,E,EL],
  rhs: Pn[N,NL,E,EL,G]) //(
  // implicit override val ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL])
    extends Eq[N,NL,E,EL,G] {
  override def toString = s"$lhs = $rhs"
}
case class ODE[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
  lhs: G[N,NL,E,EL],
  rhs: Pn[N,NL,E,EL,G]) //(
  // implicit override val ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL])
    extends Eq[N,NL,E,EL,G] {
  override def toString = s"d[$lhs]/dt = $rhs"
}

// Naming of graphs
// NOTE: It is assumed that a class extending GraphNaming will give
// the same name to all graphs in an isomorphism class.
abstract class GraphNaming[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]]//(
  // implicit val ev: G[N,NL,E,EL] <:< Graph[N,NL,E,EL])
    extends (G[N,NL,E,EL] => String) {
  // def apply(g: G[N,NL,E,EL]): String
  def seq: Seq[(G[N,NL,E,EL],String)]
}
class IncrementalNaming[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
  start: Int = 0)//(
  //implicit override val ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL])
    extends GraphNaming[N,NL,E,EL,G] {

  val cnt = Counter(start)
  val index = mutable.Map[G[N,NL,E,EL],Int]()
  val isos = mutable.Map[G[N,NL,E,EL],G[N,NL,E,EL]]()

  def apply(g: G[N,NL,E,EL]): String =
    if (index contains g) s"F${index(g)}"
    else if (isos contains g) s"F${index(isos(g))}"
    else index find { case (h,_) => g iso h } match {
      case Some((h,_)) => { isos(g) = h; s"F${index(h)}" }
      case None => { val i = cnt.next; index(g) = i; s"F$i" }
    }

  def seq: Seq[(G[N,NL,E,EL],String)] =
    for ((g,i) <- index.toSeq.sortBy(_._2)) yield (g,s"F$i")
}


class ODEPrinter[N,NL,E<:DiEdgeLike[N],EL,
  G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
  eqs: Traversable[Eq[N,NL,E,EL,G]]) { //(
  // implicit val ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) {

  // Split algebraic equations into substitutions and cancellations
  // A cancellation is a substitution by zero
  // TODO: subs and zeros should be "smart maps" that when given
  // a graph isomorphic to g and g is a key of the map, it returns
  // the value associated to g
  val subs: Map[G[N,NL,E,EL],Pn[N,NL,E,EL,G]] = eqs.collect({
    case AlgEq(lhs, rhs) if !rhs.isZero => (lhs, rhs) }).toMap

  val zeros: Set[G[N,NL,E,EL]] = eqs.collect({
    case AlgEq(lhs, rhs) if rhs.isZero => lhs }).toSet

  def substituteMn(m: Mn[N,NL,E,EL,G]): Pn[N,NL,E,EL,G] = {
    require(!hasZero(m.denom), "division by zero")
    if (hasZero(m.numer)) Pn.zero
    else {
      var changed = false
      def sub(gs: Vector[G[N,NL,E,EL]]): Pn[N,NL,E,EL,G] = {
        for (g <- gs) yield
          // TODO: I should probably check if g is iso to something in subs
          if ((subs contains g) && (subs(g) != Mn(g))) {
            changed = true
            subs(g)
          } else Pn(Mn(g))
      }.foldLeft(Pn.one[N,NL,E,EL,G])(_*_)
      val numer = sub(m.numer)
      val denom = sub(m.denom)
      val res = numer * m.coef / denom
      if (changed) substitutePn(res)
      else res
    }
  }

  def substitutePn(p: Pn[N,NL,E,EL,G]): Pn[N,NL,E,EL,G] =
    Pn(for (m1 <- p.terms; m2 <- substituteMn(m1).terms)
       yield m2).simplify

  // TODO: I should probably check if g in gs is iso to something in zeros
  def hasZero(gs: Traversable[G[N,NL,E,EL]]): Boolean =
    gs exists (zeros contains _)

  lazy val simplify: Traversable[ODE[N,NL,E,EL,G]] =
    for (ODE(lhs,rhs) <- eqs) yield ODE(lhs,substitutePn(rhs))

  def strMn[T](m: Mn[N,NL,E,EL,G], name: G[N,NL,E,EL] => T): String =
    (if (m.coef == RatePn.one) ""
     else s"${m.coef}" + (if (m.numer.isEmpty) "" else " * ")) +
     m.numer.map(name(_)).mkString(" * ") +
    (if (m.denom.isEmpty) ""
     else if (m.denom.length == 1) s" / ${name(m.denom.head)}"
     else " / (" + m.denom.map(name(_)).mkString(" * ") + ")")

  def strGraph(g: G[N,NL,E,EL]): String =
    g.toString(g.nodes.zipWithIndex.toMap)

  def print: Unit =
    print(new IncrementalNaming[N,NL,E,EL,G]())

  def print(name: GraphNaming[N,NL,E,EL,G]): Unit = {

    // TODO: Sort output
    val lines = for (ODE(lhs,rhs) <- simplify) yield (
      s"d${name(lhs)} = " + (
        if (rhs.isEmpty) "0"
        else rhs.terms.map(strMn(_,name)).mkString(" + ")))

    // Print fragments names
    for ((g,n) <- name.seq) println(s"$n := ${strGraph(g)}")
    println()

    // Print the system of diff eqs
    lines foreach (println(_))
  }

  // def saveAsOctave(filename: String, finalTime: Double, numSteps: Int,
  //   g0: G[N,NL,E,EL]): Unit =
  //   saveAsOctave(filename, 0.0, finalTime, numSteps,
  //     g => Graph.arrows(g0, g).length)

  def saveAsOctave(filename: String, finalTime: Double, numSteps: Int,
    init: G[N,NL,E,EL] => Double): Unit =
    saveAsOctave(filename, 0.0, finalTime, numSteps, init)

  def saveAsOctave(filename: String, finalTime: Double, numSteps: Int,
    init: Traversable[Double]): Unit =
    saveAsOctave(filename, 0.0, finalTime, numSteps, init)

  // def saveAsOctave(filename: String, startTime: Double,
  //   finalTime: Double, numSteps: Int, g0: G[N,NL,E,EL]): Unit =
  //   saveAsOctave(filename, startTime, finalTime, numSteps,
  //     g => Graph.arrows(g0, g).length)

  def saveAsOctave(filename: String, startTime: Double,
    finalTime: Double, numSteps: Int,
    init: G[N,NL,E,EL] => Double): Unit =
    saveAsOctave(filename, startTime, finalTime, numSteps,
      for (ODE(g,_) <- simplify) yield init(g))

  def saveAsOctave(
    filename: String,
    startTime: Double,
    finalTime: Double,
    numSteps: Int,
    init: Traversable[Double])
      : Unit = {
    val out = new java.io.PrintWriter(filename)
    val odes = simplify.toSeq // TODO: do we really need Seq to have zipWithIndex?
    out.println("# Associated graph observables:")
    val index = (for ((ODE(g, _), i) <- odes.zipWithIndex) yield
      (g, i+1)).toMap.withDefault(g => throw new MissingODE(
        "system of differential equations is not closed " +
        "(missing ODE for graph " + g + ")."))
    for ((ODE(g, _), i) <- odes.zipWithIndex)
      out.println(s"#   x(${i+1}) := ${strGraph(g)}")
    out.println("function xdot = f(x, t)")
    out.println("  # Rates:")
    val rates = (for {
      ODE(_, rhs) <- odes
      Mn(rp, _, _) <- rhs.terms
      rm <- rp.terms
      k <- rm.numer ++ rm.denom
    } yield k).toSet
    for (k <- rates)
      out.println(s"  ${k.name} = ${k.value};")
    out.println("  # ODEs:")
    for ((ODE(g, rhs), i) <- odes.zipWithIndex)
      out.println(s"  xdot(${i+1}) = " + (if (rhs.isEmpty) "0" else
        rhs.terms.map(strMn(_, h => s"x(${index(h)})")).mkString(" + ")) + ";")
    out.println("endfunction")
    out.println
    out.println("# Initial conditions:")
    out.println("x0 = " + init.mkString("[ ", ", ", " ]") + ";")
    out.println
    out.println(s"t = linspace($startTime, $finalTime, $numSteps" +
      ");  # Output times")
    out.println("x = lsode(\"f\", x0, t);  # Solve ODEs")
    out.println("printf(\"time " +
      (1 to odes.length).map(i => s"E(x($i))").mkString(" ") +
      "\\n\");  # Print header")
    out.println("printf(\"%e " +
      (1 to odes.length).map(_ => "%e").mkString(" ") +
      "\\n\", cat(1, t, " +
      (1 to odes.length).map(i => s"x(:, $i)'").mkString(", ") +
      "));  # Print data")
    out.flush
    out.close
  }

  // NOTE: Probably a good idea is to use dot2tex to generate TikZ
  // code for the graphs: https://github.com/kjellmf/dot2tex
  // def saveAsLatex(filename: String) = {
  // }
}

object ODEPrinter {
  def apply[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    eqs: Traversable[Eq[N,NL,E,EL,G]]) = //(implicit
      // ev: G[N,NL,E,EL] <:< BaseDiGraph[N,NL,E,EL]) =
    new ODEPrinter(eqs)
}

