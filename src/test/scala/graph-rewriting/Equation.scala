package graph_rewriting

import org.scalatest.{FlatSpec, Matchers}
import implicits._

class EquationSpec extends FlatSpec with Matchers {

  // -- Monomials --

  val g1 = Graph(1 -> "A")()
  val g2 = Graph(1 -> "A")()
  val g3 = g2.copy

  "A monomial" should "multiply and divide rates and graphs" in {
    val mn1 = Mn(g1)
    mn1.coef shouldBe RatePn.one
    mn1.numer shouldBe Vector(g1)
    mn1.denom shouldBe Vector()
    mn1.graphs shouldBe Seq(g1)
    val k = Rate("k")
    val mn2 = mn1 * k
    val rp = RatePn(RateMn(k))
    mn2.coef shouldBe rp
    mn2.numer shouldBe Vector(g1)
    mn2.denom shouldBe Vector()
    mn2.graphs shouldBe Seq(g1)
    val mn3 = mn2 * g2
    mn3.coef shouldBe rp
    mn3.numer shouldBe Vector(g1, g2)
    mn3.denom shouldBe Vector()
    mn3.graphs shouldBe Seq(g1, g2)
    val mn4 = mn3 / g3
    mn4.coef shouldBe rp
    mn4.numer shouldBe Vector(g1, g2)
    mn4.denom shouldBe Vector(g3)
    mn4.graphs shouldBe Seq(g1, g2, g3)
    val mn5 = -mn4
    mn5.coef shouldBe -rp
    mn5.numer shouldBe Vector(g1, g2)
    mn5.denom shouldBe Vector(g3)
    mn5.graphs shouldBe Seq(g1, g2, g3)
    val mn6 = mn5 / k
    mn6.coef shouldBe RatePn(-RateMn(k) / k)
    mn6.numer shouldBe Vector(g1, g2)
    mn6.denom shouldBe Vector(g3)
    mn6.graphs shouldBe Seq(g1, g2, g3)
  }

  it should "create a polynomial when added or substracted" in {
    val mn1 = Mn("k1", g1)
    val mn2 = Mn("k2", g2)
    val pn1 = mn1 + mn2
    pn1.terms shouldBe Vector(mn1, mn2)
    // adding monomials shouldn't change the monomials themselves
    mn1.coef shouldBe RatePn(RateMn("k1"))
    mn1.numer shouldBe Vector(g1)
    mn1.denom shouldBe Vector()
    mn2.coef shouldBe RatePn(RateMn("k2"))
    mn2.numer shouldBe Vector(g2)
    mn2.denom shouldBe Vector()
    val pn2 = mn1 - mn2
    pn2.terms shouldBe Vector(mn1, -mn2)
    // same here
    mn1.coef shouldBe RatePn(RateMn("k1"))
    mn1.numer shouldBe Vector(g1)
    mn1.denom shouldBe Vector()
    mn2.coef shouldBe RatePn(RateMn("k2"))
    mn2.numer shouldBe Vector(g2)
    mn2.denom shouldBe Vector()
  }

  it should "get equality right" in {
    val mn1 = Mn("k1", g1)
    val mn2 = Mn("k2", g2)
    mn1 should not be (mn2)
    mn1 shouldBe Mn("k1", g1)
  }

  "A polynomial" should "add and substract monomials" in {
    val mn1 = Mn(g1)
    val mn2 = Mn(g2)
    val pn1 = Pn.zero + mn1
    pn1.terms shouldBe Vector(Mn.zero, mn1)
    val pn2 = pn1 - mn2
    pn2.terms shouldBe Vector(Mn.zero, mn1, -mn2)
  }

  it should "multiply and divide numbers, graphs and monomials" in {
    val mn1 = Mn(g1)
    val mn2 = Mn(g2)
    val mn3 = Mn("k3", g3)
    val pn1 = Pn(mn1) * "k1"
    pn1.terms shouldBe Vector(Mn("k1", g1))
    val pn2 = (pn1 + mn2) * "k2"
    val k1xk2 = RatePn(RateMn("k1", "k2")) // = "k1" * "k2"
    pn2.terms shouldBe Vector(Mn(k1xk2, g1), mn2 * "k2")
    val pn3 = pn2 * g1
    pn3.terms shouldBe Vector(Mn(k1xk2, g1, g1), Mn("k2", g2, g1))
    val pn4 = pn2 * mn3
    pn4.terms shouldBe Vector(Mn(k1xk2 * "k3", g1, g3),
      Mn(RateMn("k2") * "k3", g2, g3))
    val pn5 = Pn(mn1) / "k2"
    val k2i = RateMn(Vector(), Vector[Rate]("k2"))
    pn5.terms shouldBe Vector(Mn(k2i, g1))
    val pn6 = (pn5 - mn2) / "k2"
    pn6.terms shouldBe Vector(Mn(k2i * k2i, g1), Mn(-k2i, g2))
    val pn7 = pn6 / g1
    pn7.terms shouldBe Vector(Mn(k2i * k2i, Vector(g1), Vector(g1)), // TODO: the two g1s should cancel out after simplification
      Mn(-k2i, Vector(g2), Vector(g1)))
    val pn8 = pn6 / mn3
    pn8.terms shouldBe Vector(Mn(k2i * k2i / "k3", Vector(g1), Vector(g3)),
      Mn(-k2i / "k3", Vector(g2), Vector(g3)))
    // TODO: it should also multiply other polynomials
  }

  it should "simplify" in {
    // FIXME: Implicit conversion from Graph to Mn not working here
    // val pn1 = g1 - g1
    val pn1 = Mn(g1) - g1
    pn1.simplify shouldBe Pn.zero
    val pn2 = Mn(g1) + g2 - g3 + Mn("k2", g2)
    pn2.simplify.terms shouldBe Vector(Mn(RatePn(RateMn("k2"), RateMn(1)), g1))
    val pn3 = pn2.simplify + g1
    pn3.simplify.terms shouldBe Vector(Mn(RatePn(RateMn(2), RateMn("k2")), g1))
    val g4 = Graph(2 -> "A")()
    val pn5 = Mn(g1) + g4
    pn5.simplify.terms shouldBe Vector(Mn(RateMn(2), g1))
    pn5.simplify.terms should not be (Vector(Mn(RateMn(2), g4)))
    val pn6 = Mn(g4) + g1
    pn6.simplify.terms shouldBe Vector(Mn(RateMn(2), g4))
  }

  "Equations" should "simplify" in {
    val eq1 = AlgEq(g1, Mn.zero)
    val g4 = Graph(4 -> "B")()
    val g5 = Graph(5 -> "C")()
    val g6 = Graph(6 -> "D")()
    val eq2 = AlgEq(g4, Mn(g1) * g5)
    val eq3 = ODE(g5, Mn(g4) + Mn("k2", g2) + g6)
    val eqs = ODEPrinter(List(eq1, eq2, eq3))
    eqs.subs shouldBe Map(g4 -> Mn(g1) * g5)
    eqs.zeros shouldBe Set(g1)
    // eqs.index shouldBe Map(g5 -> 0, g6 -> 1)
    eqs.simplify shouldBe List(ODE(g5, g6))
    // TODO: Check for double simplification
  }
}

