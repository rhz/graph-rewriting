package graph_rewriting

import scala.collection.mutable

class Equation[N,NL,E<:DiEdgeLike[N],EL] {

  type G = Graph[N,NL,E,EL]
  type Eqs = Vector[Equation]

  /** Graph monomials. */
  case class Monomial(factor: Double,
    numer: Vector[G], denom: Vector[G]) {

    def * (n: Double) = Monomial(factor * n, numer, denom)
    def / (n: Double) = Monomial(factor / n, numer, denom)
    def * (m: Monomial) = Monomial(factor * m.factor, numer ++ m.numer, denom ++ m.denom)
    def / (m: Monomial) = Monomial(factor / m.factor, numer ++ m.denom, denom ++ m.numer)
    def * (g: G) = Monomial(factor, numer :+ g, denom)
    def / (g: G) = Monomial(factor, numer, denom :+ g)
    def * (gs: Traversable[G]) = Monomial(factor, numer ++ gs, denom)
    def / (gs: Traversable[G]) = Monomial(factor, numer, denom ++ gs)
    def unary_- = Monomial(-factor, numer, denom)
    def graphs: Seq[G] = numer ++ denom
  }

  /** Graph polynomials. */
  case class Polynomial(terms: Vector[Monomial]) {
    def + (m: Monomial)   = Polynomial(terms :+  m)
    def - (m: Monomial)   = Polynomial(terms :+ -m)
    def + (p: Polynomial) = Polynomial(terms ++   p .terms)
    def - (p: Polynomial) = Polynomial(terms ++ (-p).terms)
    def unary_- = Polynomial(terms map (_ * -1))
    def graphs: Seq[G] = terms flatMap (_.graphs)

    import Graph._

    def simplify: Polynomial = {
      val factorOf = mutable.Map.empty[(Vector[G], Vector[G]), Double]
      for (Monomial(f1, n1, d1) <- terms) {
        factorOf find {
          case ((n2, d2), _) => isos(n1, n2) && isos(d1, d2)
        } match {
          case Some((m, f2)) => factorOf(m) = f1 + f2
          case None => factorOf((n1, d1)) = f1
        }
      }
      Polynomial((
        for (((ns, ds), f) <- factorOf if (f <= -eps) || (f >= eps))
        yield Monomial(f, ns, ds)).toVector)
    }

    val eps: Double = 1e-16

    override def toString = "Polynomial(" + terms + ")"
    // if (terms.isEmpty) "0"
    // else terms.mkString(" + ").replace("+ -", "- ")
  }

  // -- Implicits --
  implicit def numToMonomial(n: Double) =
    Monomial(n, Vector(), Vector())
  implicit def numToPolynomial(n: Double) =
    Polynomial(Vector(numToMonomial(n)))
  implicit def graphToMonomial(g: G) =
    Monomial(1, Vector(g), Vector())
  implicit def graphToPolynomial(g: G) =
    Polynomial(Vector(graphToMonomial(g)))
  implicit def monomialToPolynomial(m: Monomial) =
    Polynomial(Vector(m))

  sealed abstract class Equation
  case class AlgEquation(lhs: G, rhs: Polynomial)
      extends Equation {
    override def toString = lhs.toString + " = " + rhs
  }
  case class ODE(lhs: G, rhs: Polynomial)
      extends Equation {
    override def toString = "d[" + lhs + "]/dt = " + rhs
  }

  def printEqs(eqs: Traversable[Equation]): Unit = {

    // Split algebraic equations into substitutions and cancellations
    val (ae0, ae1) = eqs.filter(_.isInstanceOf[AlgEquation]) partition {
      case AlgEquation(_, rhs) => rhs.terms.isEmpty }
    val zeros = ae0.map({ case AlgEquation(lhs, _) => lhs }).toSet
    val subs = ae1.map({ case AlgEquation(lhs, rhs) => (lhs, rhs) }).toMap

    var i = 0
    def newName: String = { i += 1; "F" + i }

    val lhss = eqs.collect({ case ODE(lhs, _) => lhs }).toSet

    // Assign names to graphs
    val names: Map[G, String] = {
      (for (ODE(lhs, _) <- eqs) yield (lhs, newName)) ++
      // FIXME
      (for (ODE(_, rhs) <- eqs; m <- rhs.terms; g <- m.graphs)
        // if !(zeros contains g) && !(subs contains g) && !(lhss contains g))
       yield (g, newName)) ++
      (for (AlgEquation(_, rhs) <- ae1; m <- rhs.terms; g <- m.graphs)
        // if !(zeros contains g) && !(subs contains g) && !(lhss contains g))
       yield (g, newName)) ++
      (for (AlgEquation(lhs, _) <- ae1) yield (lhs, newName))
    }.toMap

    // Print those names
    for ((g, name) <- names.toSeq.sortBy(_._2.tail.toInt))
      println(name + " := " + g)
    println()

    // println("zeros:")
    // for (z <- zeros) println("  " + z)
    // println()

    // Print the system of diff eqs
    for (ODE(lhs, rhs) <- eqs) {
      print("d" + names(lhs) + " = ")
      for (m <- rhs.terms) {
        if (m.denom exists (zeros contains _))
          throw new IllegalArgumentException("division by zero")

        if (!(m.numer exists (zeros contains _))) {

          def expand(queue: Vector[(G, Boolean)],
            factor: Double, numer: Seq[G], denom: Seq[G])
              : (Double, Seq[G], Seq[G]) = queue match {
            case Vector() => (factor, numer, denom)
            case (g, dividing) +: tl =>
              if (subs contains g) {
                val p = subs(g)
                assume(p.terms.length == 1,
                  "I don't know how to handle this yet, ask Ricardo")
                val sub = p.terms.head
                if (sub.numer.nonEmpty)
                  assume(sub.numer(0) ne (g),
                    "something's fishy here: " + g + " ne " + sub)
                if (dividing) { // when dividing
                  expand(tl ++ (sub.numer.map(g => (g, true)) ++ // numer go to the top
                    sub.denom.map(g => (g, false))), // and denom to the bottom
                    factor / sub.factor, numer, denom)
                } else {
                  expand(tl ++ (sub.numer.map(g => (g, false)) ++
                    sub.denom.map(g => (g, true))),
                    factor * sub.factor, numer, denom)
                }
              } else if (dividing) {
                expand(tl, factor, numer, denom :+ g)
              } else {
                expand(tl, factor, numer :+ g, denom)
              }
          }

          val (factor, numer, denom) = expand(
            m.numer.map(g => (g, false)) ++
              m.denom.map(g => (g, true)),
            m.factor, Vector(), Vector())

          if (m.factor < 0) print(" - ")
          else print(" + ")
          print(factor.abs)
          for (g <- numer) print(" * " + names(g))
          if (denom.nonEmpty) {
            print(" / (" + names(denom.head))
            for (g <- denom.tail) print(" * " + names(g))
            print(")")
          }
        }
      }
      println()
    }
  }
}
