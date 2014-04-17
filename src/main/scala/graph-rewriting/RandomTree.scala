package graph_rewriting

import annotation.tailrec

import util.Random


/**
 * This is a simplified version of the ''random tree'' data structure
 * used by KaSim (see [[https://github.com/jkrivine/KaSim/blob/master/dataStructures/random_tree.ml]]).
 *
 * The random tree data structure represents a distribution over the
 * integer interval `{0, 1 ... size - 1}` as a sequence of `size`
 * double-precision floaing-point weight values.  (The weights are
 * stored in the leaves of a binary tree -- hence the name).  The
 * [[nextRandom]] method can be used to sample the distribution:
 * [[nextRandom]] picks a random element from the interval, with
 * probability proportional to the weight of the element.
 *
 * Unlike the random trees used by KaSim, instances of this class
 * represent fixed-size random trees, that is, the size of the tree is
 * fixed at creation time and can not be modified afterwards.
 * However, instances of this tree remain mutable in that the weights
 * of the leaves of the random tree can be updated after creation.
 *
 * Usage examples:
 *
 * {{{
 *   // Create a random tree
 *   val rt = RandomTree(List(1.0, 2.0, 3.0), new scala.util.Random)
 *
 *   // Histogram of random trials
 *   val hist1 = new Array[Int](3)
 *   for (_ <- 0 until 10000) hist1(rt.nextRandom._1) += 1
 *   hist1 // e.g. hist1: Array[Int] = Array(1657, 3252, 5091)
 *
 *   // Histogram of infinitely biased trials
 *   val hist2 = new Array[Int](3)
 *   rt(2) = Double.PositiveInfinity
 *   for (_ <- 0 until 10000) hist2(rt.nextRandom._1) += 1
 *   hist2 // hist2: Array[Int] = Array(0, 0, 10000)
 * }}}
 *
 * @constructor creates a random tree with `size` leafs the weights
 *              of which are initialized to zero.
 *
 * @param weights the sequence of values used to initialize the
 *                leaf weights.  
 *
 * @param prng the the pseudo-random number generator used by the
 *             random tree to generate random numbers.
 */
class RandomTree(val size: Int, val prng: Random) {

  /**
   * The array holding the weights of the nodes of the tree.
   * Successive elements correspond to the nodes of the (binary) tree
   * in a breath-first traversal order.  The elements of `weights`
   * with indices from 0 up to `(leavesOffset - 1)` correspond to
   * internal nodes, while elements with indices above `leavesOffset`
   * correspond to leave nodes.
   */
  private val weights = new Array[Double](2 * size - 1)

  /** The index of the first leaf weight in the `weights` array. */
  private val leavesOffset = size - 1

  /**
   * Select the weight of the `i`th leaf of the random tree.
   *
   * @param i the index of the leaf to select.
   * @return the weight of the `i`th leaf of the random tree.
   */
  def apply(i: Int) = weights(leavesOffset + i)
  
  /**
   * Assign a new weight to the `i`th leaf of the random tree.
   *
   * @param i the index of the leaf to update.
   * @param w the new weight of the `i`th leaf of the random tree.
   */
  def update(i: Int, w: Double) {
    updateParentWeights(leavesOffset + i, w)
  }

  /**
   * Check whether the `i`th leaf of the random tree has infinite weight.
   *
   * @return `true` if the `i`th leaf of the random tree has infinite
   *         weight, `false` otherwise.
   */
  @inline def isInfinite(i: Int) = isInfNode(leavesOffset + i)

  /**
   * Returns the sum of all the weights of the leaves of the random tree.
   *
   * @return the sum of all the weights of the leaves of the random tree.
   */
  def totalWeight = weights(0)

  /**
   * Returns the index and weight of a random leaf of the random tree
   * with probability proportional to the weight of that leaf.
   *
   * More precisely, the probability of selecting leaf `i` is
   *
   * {{{
   *   P(i) = this.apply(i) / this.totalWeight
   * }}}
   *
   * @return the index and weight of a random leaf of the random tree
   *         with probability proportional to the weight of that leaf.
   */
  def nextRandom: Int =
    if (isInfNode(0)) findInfLeaf(0)
    else {
      val tw = totalWeight
      if (tw == 0.0) throw new NoSuchElementException
      val r = prng.nextDouble * tw
      findRandomLeaf(0, r)
    }

  /**
   * Returns a string containing the leaf weights of this random tree.
   *
   * @return a string containing the leaf weights of this random tree.
   */
  override def toString =
    weights drop leavesOffset mkString ("RandomTree(", ",", ")")

  /**
   * Helper function to update the weights of (inner) parent nodes
   * after an update to a leaf.
   */
  @tailrec
  private def updateParentWeights(i: Int, w: Double) {
    weights(i) = w
    if (i > 0) {
      val pi = parent(i)
      val li = leftChild(pi)
      val ri = rightChild(pi)
      updateParentWeights(pi, weights(li) + weights(ri))
    }
  }

  /**
   * Helper function to find the a leaf node for a particular random
   * trial.
   */
  @tailrec
  private def findRandomLeaf(i: Int, x: Double): Int =
    if (isLeaf(i)) i - leavesOffset
    else {
      val li = leftChild(i)
      val lw = weights(li)
      if (x < lw) findRandomLeaf(li, x)
      else findRandomLeaf(rightChild(i), x - lw)
    }
      
  /** Helper function to find any leaf node with infinite weight. */
  @tailrec
  private def findInfLeaf(i: Int): Int =
    if (isLeaf(i)) i - leavesOffset
    else {
      val li = leftChild(i)
      if (isInfNode(li)) findInfLeaf(li)
      else findInfLeaf(rightChild(i))
    }

  /**
   * Helper function to compute the weights of (inner) parent nodes
   * at construction time.
   */
  @tailrec
  private def initParentWeights(s: Int): Unit =
    if (s > 0) {
      val s2 = parent(s)
      for (i <- (s - 1) to s2 by -1) {
        weights(i) = weights(leftChild(i)) + weights(rightChild(i))
      }
      initParentWeights(s2)
    }

  /** Returns the index of the parent of the node with index `i`. */
  @inline private def parent(i: Int) = (i - 1) / 2 

  /** Returns the index of the left child of the node with index `i`. */
  @inline private def leftChild(i: Int) = i * 2 + 1 

  /** Rreturns the index of the right child of the node with index `i`. */
  @inline private def rightChild(i: Int) = i * 2 + 2 

  /** Returns `true` if the node with index `i` has infinite weight. */
  @inline private def isInfNode(i: Int) =
    weights(i) == Double.PositiveInfinity

  /** Returns `true` if the node with index `i` if a leaf. */
  @inline private def isLeaf(i: Int) = i >= leavesOffset
}


/** Factory methods for [[RandomTree]].  For example:
 *
 * {{{
 *   // Create a random tree with initial weights (1, 2, 3)
 *   val rt = RandomTree(List(1.0, 2.0, 3.0), new scala.util.Random)
 * }}}
 */
object RandomTree {

  /**
   * Creates a random tree with `size` leafs the weights of which are
   * initialized to zero.
   *
   * @param size the number of leaves in this random tree.  
   *
   * @param prng the the pseudo-random number generator used by the
   *             random tree to generate random numbers.
   *
   * @return a random tree with `size` leafs the weights of which
   *         are initialized to zero.
   */
  def apply(size: Int, prng: Random) = new RandomTree(size, prng)

  /**
   * Creates a random tree with the leaf weights initialized to the
   * values given in `weights`.
   *
   * @param weights the sequence of values used to initialize the
   *                leaf weights.  
   *
   * @param prng the the pseudo-random number generator used by the
   *             random tree to generate random numbers.
   *
   * @return a random tree with the leaf weights initialized to the
   *         values given in `weights`.
   */
  def apply(weights: Seq[Double], prng: Random) = {
    val rt = new RandomTree(weights.size, prng)
    weights.copyToArray(rt.weights, rt.leavesOffset)
    rt.initParentWeights(rt.leavesOffset)
    rt
  }
}

