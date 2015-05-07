package graph_rewriting

import scala.collection.mutable

class Simulator[N,NL,E<:DiEdgeLike[N],EL] {

  type G = DiGraph[N,NL,E,EL]
  type A = Arrow[N,NL,E,EL,N,NL,E,EL,DiGraph]
  type R = Rule[N,NL,E,EL,DiGraph]
  val rules: Seq[R] = List()

  // --- State ---

  type State = G
  val state: State = new DiGraph[N,NL,E,EL]
  val matches = mutable.Map.empty[G,Seq[A]]

  var time: Double = 0.0
  var events: Long = 0
  var _maxTime: Option[Double] = None
  var _maxEvents: Option[Long] = None

  /** Set the maximum time for the simulation. */
  def maxTime_= (t: Double) = { _maxTime = Some(t) }
  @inline def maxTime = _maxTime

  /** Set the maximum number of events for the simulation. */
  def maxEvents_= (e: Long) = { _maxEvents = Some(e) }
  @inline def maxEvents = _maxEvents

  // Create a new random number generator
  val rand = new util.Random

  /** Pick a random element of the sequence. */
  def randomElement[A](xs: Seq[A]): A =
    xs(rand.nextInt(xs.length))

  /** Simulate. */
  def run {

    // Main loop
    while ((events < (maxEvents getOrElse (events + 1))) &&
           (time < (maxTime getOrElse Double.PositiveInfinity))) {

      // Compute rule propensities
      val propensities = for (r <- rules) yield
        (r.rate.value * matches(r.lhs).length)

      // Build the propensity tree
      val tree = RandomTree(propensities, rand)
      val totalProp = tree.totalWeight

      if (totalProp == 0 || totalProp.isNaN)
        throw new IllegalStateException("no more events")
      
      // Advance time
      val dt = -math.log(rand.nextDouble) / totalProp
      time += dt

      // Pick a rule and event at random
      val r = rules(tree.nextRandom)
      val e = randomElement(matches(r.lhs))

      // Apply the rule/event
      // ...
    }
  }
}

