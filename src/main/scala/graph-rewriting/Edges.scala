package graph_rewriting

import scala.collection.Set

abstract class EdgeLike[N] {
  def nodes: Set[N]
  def contains(n: N): Boolean
  def arity: Int
  def isDirected: Boolean
  def isHyperEdge: Boolean
  def isLooping: Boolean
  final def isUndirected = !isDirected
  final def nonHyperEdge = !isHyperEdge
  final def nonLooping = !isLooping
}

trait DiEdgeLike[N] extends EdgeLike[N] {
  def source: N
  def target: N
  def nodes = Set(source, target)
  def contains(n: N) = (source == n) || (target == n)
  def arity = 2
  def isDirected = true
  def isHyperEdge = false
  def isLooping = source == target
}

case class DiEdge[N](source: N, target: N) extends DiEdgeLike[N]

object ~> {
  def unapply[N](e: DiEdge[N]): Option[(N, N)] =
    if (e eq null) None else Some((e.source, e.target))
}

// For multigraphs
case class IdDiEdge[I,N](id: I, source: N, target: N) extends DiEdgeLike[N]

// Fancy syntax for IdDiEdge?

