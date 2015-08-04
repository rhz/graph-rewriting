package uk.ac.ed.inf
package graph_rewriting

import scala.math.BigInt
import scala.math.BigDecimal

import scala.collection.mutable.MutableList

import graph_rewriting._
/**
 * @author theindel
 *
 */
object MyLittleFunTaylorThingy {

  case class Summand[GT](
      val integerFact: BigInt,
      val combinedRate: BigDecimal,
      val g: GT) {
    // empty --- just a data type
    override def toString () ={ 
      integerFact.toString() + "." + 
      combinedRate.toString() + "*" + g
    }
  }

  def computeTaylorCoeffs[N, NL, E <: DiEdgeLike[N], EL, H[X, Y, Z <: DiEdgeLike[X], W] <: ConcreteDiGraph[X, Y, Z, W, H]](
    order: Int,
    rules: Traversable[Rule[N, NL, E, EL, H]],
    observable: H[N, NL, E, EL])(implicit nodeUnifier: Unifier[N, N, N],
                                 edgeUnifier: (H[N, NL, E, EL], Map[N, N], Map[N, N]) => Unifier[E, E, E],
                                 graphBuilder: () => H[N, NL, E, EL]) // ev: H[N,NL,E,EL]#This <:< H[N,NL,E,EL]) // WARNING: This breaks the compiler
                                 : (List[Summand[H[N, NL, E, EL]]], List[H[N, NL, E, EL]]) = {

    type LinearComb = List[Summand[H[N, NL, E, EL]]]

    if (order == 0) {
      println("the 0-th truncation" + Summand(1, 1, observable))
      return (List(Summand(1, 1, observable)), List(observable))
    } else {

      @inline
      def isoSubst(known: MutableList[H[N, NL, E, EL]], toCheck: H[N, NL, E, EL]): H[N, NL, E, EL] = {
        val filtered = known.filter(elem => elem.iso(toCheck))

        if (filtered.isEmpty) {
          toCheck
        } else {
          if (filtered.size > 1) {
            System.err.println("error: list of frags not repetition free up to iso")
          }
          known += filtered.head;
          filtered.head
        }
      }
      // recursive call 
      val previous = computeTaylorCoeffs(order - 1, rules, observable)
      val (linComb, frags) = previous

      val fragCol: MutableList[H[N, NL, E, EL]] = new MutableList();
      fragCol ++= frags;
      val listOfResults: List[Traversable[Seq[Summand[H[N, NL, E, EL]]]]] =
        linComb.map(summand =>
          for (rl <- rules) yield {
            summand.g.leftUnions(rl).map(lmg =>
              Summand(-1, rl.rate.value, isoSubst(fragCol, lmg))) ++
              summand.g.rightUnions(rl).map(rmgX =>
                Summand(1, rl.rate.value, isoSubst(fragCol, rmgX)))
          })
      //       val result: List[Summand[H[N,NL,E,EL]]] = 
      //         for (summand <- previous) yield 
      //           for (r <- rules ) yield {
      //          summand.g.leftUnions(r)
      //       }

      val theResultList = listOfResults.flatten.flatten;
      println("the " + order + "-th truncation")
      theResultList.map(x => println("the next summand " + x))
      
      (theResultList, fragCol.toList)
    }
  }
}