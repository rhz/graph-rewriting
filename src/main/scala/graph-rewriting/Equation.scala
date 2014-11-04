package graph_rewriting

import scala.collection.mutable
import utils.Counter

/** Graph monomials. */
class Mn[N,NL,E<:DiEdgeLike[N],EL](
  val coef: Double,
  val numer: Vector[Graph[N,NL,E,EL]],
  val denom: Vector[Graph[N,NL,E,EL]]) {
  // multiplication and division
  def * (n: Double) = Mn[N,NL,E,EL](coef * n, numer, denom)
  def / (n: Double) = Mn[N,NL,E,EL](coef / n, numer, denom)
  def * (g: Graph[N,NL,E,EL]) = Mn[N,NL,E,EL](coef, numer :+ g, denom)
  def / (g: Graph[N,NL,E,EL]) = Mn[N,NL,E,EL](coef, numer, denom :+ g)
  def * (m: Mn[N,NL,E,EL]) = Mn[N,NL,E,EL](coef * m.coef, numer ++ m.numer, denom ++ m.denom)
  def / (m: Mn[N,NL,E,EL]) = Mn[N,NL,E,EL](coef / m.coef, numer ++ m.denom, denom ++ m.numer)
  def * (p: Pn[N,NL,E,EL]): Pn[N,NL,E,EL] = p map (_ * this)
  def / (p: Pn[N,NL,E,EL]): Pn[N,NL,E,EL] = p map (_ / this)
  // addition and substraction
  def + (m: Mn[N,NL,E,EL]) = Pn[N,NL,E,EL](Vector(this,  m))
  def - (m: Mn[N,NL,E,EL]) = Pn[N,NL,E,EL](Vector(this, -m))
  def + (p: Pn[N,NL,E,EL]) = Pn[N,NL,E,EL](this +:   p .terms)
  def - (p: Pn[N,NL,E,EL]) = Pn[N,NL,E,EL](this +: (-p).terms)
  def unary_- = Mn(-coef, numer, denom)
  // equality
  override def equals(other: Any): Boolean = other match {
    case that: Mn[_,_,_,_] =>
      (that canEqual this) &&
      (coef == that.coef) &&
      (numer == that.numer) &&
      (denom == that.denom)
    case _ => false
  }
  def canEqual(other: Any): Boolean =
    other.isInstanceOf[Mn[_,_,_,_]]
  override def hashCode: Int =
    41 * (41 * (41 + coef.hashCode) + numer.hashCode) + denom.hashCode
  def graphs: Seq[Graph[N,NL,E,EL]] = numer ++ denom
  override def toString = s"Mn($coef, $numer, $denom)"
}

object Mn {
  def apply[N,NL,E<:DiEdgeLike[N],EL]() =
    new Mn[N,NL,E,EL](1.0, Vector(), Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL](coef: Double) =
    new Mn[N,NL,E,EL](coef, Vector(), Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL](numer: Graph[N,NL,E,EL]*) =
    new Mn[N,NL,E,EL](1.0, numer.toVector, Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL](numer: Vector[Graph[N,NL,E,EL]]) =
    new Mn[N,NL,E,EL](1.0, numer, Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL](numer: Traversable[Graph[N,NL,E,EL]]) =
    new Mn[N,NL,E,EL](1.0, numer.toVector, Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL](coef: Double, numer: Graph[N,NL,E,EL]*) =
    new Mn[N,NL,E,EL](coef, numer.toVector, Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL](coef: Double,
    numer: Vector[Graph[N,NL,E,EL]]) =
    new Mn[N,NL,E,EL](coef, numer, Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL](coef: Double,
    numer: Traversable[Graph[N,NL,E,EL]]) =
    new Mn[N,NL,E,EL](coef, numer.toVector, Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL](coef: Double,
    numer: Vector[Graph[N,NL,E,EL]],
    denom: Vector[Graph[N,NL,E,EL]]) =
    new Mn[N,NL,E,EL](coef, numer, denom)
  def apply[N,NL,E<:DiEdgeLike[N],EL](coef: Double,
    numer: Traversable[Graph[N,NL,E,EL]],
    denom: Traversable[Graph[N,NL,E,EL]]) =
    new Mn[N,NL,E,EL](coef, numer.toVector, denom.toVector)
  def unapply[N,NL,E<:DiEdgeLike[N],EL](m: Mn[N,NL,E,EL]): Option[(
    Double, Vector[Graph[N,NL,E,EL]], Vector[Graph[N,NL,E,EL]])] =
    Some(m.coef, m.numer, m.denom)
}


/** Graph polynomials. */
class Pn[N,NL,E<:DiEdgeLike[N],EL](val terms: Vector[Mn[N,NL,E,EL]]) {
  // addition and substraction
  def + (m: Mn[N,NL,E,EL]) = Pn[N,NL,E,EL](terms :+  m)
  def - (m: Mn[N,NL,E,EL]) = Pn[N,NL,E,EL](terms :+ -m)
  def + (p: Pn[N,NL,E,EL]) = Pn[N,NL,E,EL](terms ++   p .terms)
  def - (p: Pn[N,NL,E,EL]) = Pn[N,NL,E,EL](terms ++ (-p).terms)
  def unary_- = Pn[N,NL,E,EL](terms map (_ * -1))
  // multiplication and division
  def * (n: Double): Pn[N,NL,E,EL] = * (Mn[N,NL,E,EL](n))
  def / (n: Double): Pn[N,NL,E,EL] = / (Mn[N,NL,E,EL](n))
  def * (g: Graph[N,NL,E,EL]): Pn[N,NL,E,EL] = * (Mn(g))
  def / (g: Graph[N,NL,E,EL]): Pn[N,NL,E,EL] = / (Mn(g))
  def * (m: Mn[N,NL,E,EL]): Pn[N,NL,E,EL] = map(_ * m)
  def / (m: Mn[N,NL,E,EL]): Pn[N,NL,E,EL] = map(_ / m)
  def * (p: Pn[N,NL,E,EL]): Pn[N,NL,E,EL] =
    (for (m1 <- terms; m2 <- p.terms) yield m1 * m2).foldLeft(
      Pn.empty[N,NL,E,EL])(_+_)
  def / (p: Pn[N,NL,E,EL]): Pn[N,NL,E,EL] =
    (for (m1 <- terms; m2 <- p.terms) yield m1 / m2).foldLeft(
      Pn.empty[N,NL,E,EL])(_+_)
  // equality
  override def equals(other: Any): Boolean = other match {
    case that: Pn[_,_,_,_] =>
      (that canEqual this) && terms == that.terms
    case _ => false
  }
  def canEqual(other: Any): Boolean =
    other.isInstanceOf[Pn[_,_,_,_]]
  override def hashCode: Int = terms.hashCode

  // -- Seq methods --
  def isEmpty = terms.isEmpty
  def nonEmpty = terms.nonEmpty
  def map(f: Mn[N,NL,E,EL] => Mn[N,NL,E,EL]) = Pn(terms map f)

  // -- Pn methods --
  def graphs: Seq[Graph[N,NL,E,EL]] = terms flatMap (_.graphs)
  val eps: Double = 1e-16
  def simplify: Pn[N,NL,E,EL] = {
    import Graph.isos
    val mns = mutable.ArrayBuffer.empty[Mn[N,NL,E,EL]]
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
    Pn(mns.filter(m => (m.coef <= -eps) || (m.coef >= eps)).toVector)
  }
    // immutable version of `simplify`... but it doesn't work
    // Pn(terms.foldLeft(Vector.empty[Mn[N,NL,E,EL]]) ({
    //   case (res1, m1) => {
    //     val Mn(c1, n1, d1) = m1
    //     // check if m1 is "iso" to a term in res1
    //     // if it is, update the coefficient of that term
    //     val (found, res2) = res1.foldLeft((false, res1)) ({
    //       case ((found, res2), m2) => {
    //         val Mn(c2, n2, d2) = m2
    //         if (!found || (Graph.isos(n1, n2) && Graph.isos(d1, d2)))
    //           (true, res2 :+ Mn(c1 + c2, n2, d2))
    //         else (found, res2 :+ m2)
    //       }
    //     })
    //     if (found) res2
    //     else res1 :+ m1
    //   }
    // }).filter(m => (m.coef <= -eps) || (m.coef >= eps)))

  override def toString = s"Pn($terms)"
  // terms.mkString(" + ").replace("+ -", "- ")
}

object Pn {
  def empty[N,NL,E<:DiEdgeLike[N],EL]: Pn[N,NL,E,EL] =
    new Pn[N,NL,E,EL](Vector())
  def apply[N,NL,E<:DiEdgeLike[N],EL](): Pn[N,NL,E,EL] = empty
  def apply[N,NL,E<:DiEdgeLike[N],EL](terms: Mn[N,NL,E,EL]*) =
    new Pn[N,NL,E,EL](terms.toVector)
  def apply[N,NL,E<:DiEdgeLike[N],EL](terms: Traversable[Mn[N,NL,E,EL]]) =
    new Pn[N,NL,E,EL](terms.toVector)
  def unapply[N,NL,E<:DiEdgeLike[N],EL](p: Pn[N,NL,E,EL])
      : Option[Vector[Mn[N,NL,E,EL]]] = Some(p.terms)
}

sealed abstract class Eq[N,NL,E<:DiEdgeLike[N],EL] {
  val lhs: Graph[N,NL,E,EL]
  val rhs: Pn[N,NL,E,EL]
}
case class AlgEq[N,NL,E<:DiEdgeLike[N],EL](lhs: Graph[N,NL,E,EL], rhs: Pn[N,NL,E,EL])
    extends Eq[N,NL,E,EL] {
  override def toString = s"$lhs = rhs"
}
case class ODE[N,NL,E<:DiEdgeLike[N],EL](lhs: Graph[N,NL,E,EL], rhs: Pn[N,NL,E,EL])
    extends Eq[N,NL,E,EL] {
  override def toString = s"d[$lhs]/dt = $rhs"
}

class Eqs[N,NL,E<:DiEdgeLike[N],EL](eqs: Traversable[Eq[N,NL,E,EL]]) {

  // Split algebraic equations into substitutions and cancellations
  val subs: Map[Graph[N,NL,E,EL], Pn[N,NL,E,EL]] = eqs.collect({
    case AlgEq(lhs, rhs) if rhs.nonEmpty => (lhs, rhs) }).toMap
  val zeros: Set[Graph[N,NL,E,EL]] = eqs.collect({
    case AlgEq(lhs, Pn(Vector())) => lhs }).toSet

  // Assign an index to graphs
  val index: Map[Graph[N,NL,E,EL], Int] = {
    val lhss = eqs.collect({ case ODE(lhs, _) => lhs }).toSet
    val cnt = Counter()
    (for (ODE(lhs, _) <- eqs) yield (lhs, cnt.next)) ++
    (for (ODE(_, rhs) <- eqs; g <- rhs.graphs
      if !(zeros contains g) && !(subs contains g) && !(lhss contains g))
     yield (g, cnt.next)) ++
    (for (rhs <- subs.values; g <- rhs.graphs
      if !(zeros contains g) && !(subs contains g) && !(lhss contains g))
     yield (g, cnt.next))
  }.toMap

  def isZero(xs: Traversable[Graph[N,NL,E,EL]]): Boolean =
    xs exists (zeros contains _)

  def substitute(m: Mn[N,NL,E,EL]): Pn[N,NL,E,EL] = {
    require(!isZero(m.denom), "division by zero")
    if (isZero(m.numer)) Pn.empty
    else {
      var changed = false
      def sub(gs: Traversable[Graph[N,NL,E,EL]]) = {
        for (g <- gs) yield
          if ((subs contains g) && (subs(g) != Pn(Mn(g)))) {
            changed = true
            subs(g)
          } else Pn(Mn(g))
      }.foldLeft(Pn(Mn[N,NL,E,EL]()))(_*_)
      val numer = sub(m.numer)
      val denom = sub(m.denom)
      val res = Mn(m.coef) * numer / denom
      if (changed) (for (m1 <- res.terms; m2 <- substitute(m1).terms)
                    yield m2).foldLeft(Pn.empty[N,NL,E,EL])(_+_)
      else res
    }
  }

  def simplify: Traversable[ODE[N,NL,E,EL]] =
    for (ODE(lhs, rhs) <- eqs) yield
      ODE(lhs, Pn(for (m1 <- rhs.terms; m2 <- substitute(m1).terms)
                  yield m2).simplify)

  def printEqs: Unit = {

    // Print fragments names
    for ((g, i) <- index.toSeq.sortBy(_._2))
      println(s"F$i := $g")
    println()

    // Print the system of diff eqs
    for (ODE(lhs, rhs) <- simplify) {
      print(s"dF${index(lhs)} =")
      if (rhs.isEmpty) print(" 0")
      else for (Mn(coef, numer, denom) <- rhs.terms) {
        if (coef < 0) print(" - ")
        else print(" + ")
        print(coef.abs)
        for (g <- numer) print(" * F" + index(g))
        if (denom.nonEmpty) {
          print(" / (F" + index(denom.head))
          for (g <- denom.tail) print(" * F" + index(g))
          print(")")
        }
      }
      println()
    }
  }
}

