package graph_rewriting

import utils.Counter

object implicits {

  // -- Nodes --
  def next(xs: Traversable[Int]) = if (xs.isEmpty) 0 else (xs.max + 1)

  implicit def newIntNode(g: Graph[Int,_,_,_]): Int = next(g.nodes)

  implicit def newStringNode(g: Graph[String,_,_,_]): String = {
    val id = util.Random.nextString(10)
    if (g.nodes contains id) newStringNode(g)
    else id
  }


  // -- Edges --
  final implicit class DiEdgeConst[N](n1: N) {
    def ~> (n2: N) = DiEdge(n1,n2)
  }

  final implicit class IdDiEdgeConst[N](n1: N) {
    def ~~> (n2: N) = IdDiEdge(Counter.next,n1,n2)
  }

  implicit def newIdDiEdge[N](g: DiGraph[N,_,IdDiEdge[Int,N],_],
    u: N, v: N) = new IdDiEdge(next(g(u) edgesTo v collect {
      case IdDiEdge(id,_,_) => id }), u, v)


  // -- Maps --
  final implicit class InvertibleMap[A,B](m: Map[A,B]) {
    def inverse = m map (_.swap)
  }


  // -- Rate monomials and polynomials --
  implicit def nameToRate(name: String) = Rate(name)
  // By not implicitly converting to RateMn we can use RatePn.* method
  // implicit def nameToRMn(name: String) = RateMn(Rate(name))
  // implicit def rateToRMn(k: Rate) = RateMn(k)
  implicit def nameToRPn(name: String) = RatePn(RateMn(Rate(name)))
  implicit def rateToRPn(k: Rate) = RatePn(RateMn(k))
  implicit def rateMnToRPn(rm: RateMn) = RatePn(rm)


  // -- Graph monomials and polynomials --
  // Rates don't have required type information
  // implicit def nameToMn(name: String) = Mn(name)
  // implicit def nameToPn(name: String) = Pn(Mn(name))
  // implicit def rateToMn(k: Rate) = Mn(k)
  // implicit def rateToPn(k: Rate) = Pn(Mn(k))
  // implicit def rateMnToMn(rm: RateMn) = Mn(rm)
  // implicit def rateMnToPn(rm: RateMn) = Pn(Mn(rm))
  // implicit def ratePnToMn(rp: RatePn) = Mn(rp)
  // implicit def ratePnToPn(rp: RatePn) = Pn(Mn(rp))
  implicit def graphToMn[N,NL,E<:DiEdgeLike[N],EL](
    g: DiGraph[N,NL,E,EL]): Mn[N,NL,E,EL,DiGraph] = Mn(g)
  implicit def graphToPn[N,NL,E<:DiEdgeLike[N],EL](
    g: DiGraph[N,NL,E,EL]): Pn[N,NL,E,EL,DiGraph] =
    Pn[N,NL,E,EL,DiGraph](Mn(g))
  implicit def mnToPn[N,NL,E<:DiEdgeLike[N],EL](
    m: Mn[N,NL,E,EL,DiGraph]) = Pn[N,NL,E,EL,DiGraph](m)


  // -- Graph --
  implicit def withLabel[T,U](x: (T,U)) = (x._1,Some(x._2))
  implicit def withoutLabel[T,U](x: T): (T,Option[U])  = (x,None)
  implicit def toSome[T](x: T) = Some(x)


  // -- Unify nodes and edges --
  implicit object StringNodeUnifier
      extends DiGraph.Unifier[String,String,String] {
    def unify(u: String, v: String) = s"($u,$v)"
    def left(u: String) = s"($u,)"
    def right(u: String) = s"(,$u)"
  }

  implicit object IdDiEdgeUnifier
      extends DiGraph.EdgeUnifier[String,String,String,
        IdDiEdge[Int,String],IdDiEdge[Int,String],IdDiEdge[Int,String]] {
    def unify(e1: IdDiEdge[Int,String], e2: IdDiEdge[Int,String]) =
      IdDiEdge(Counter.next,e1.source,e1.target)
    var cnt: Counter = null
    var fn1: Map[String,String] = null
    var fn2: Map[String,String] = null
    def initialise[NL,EL,G[X,Y,Z<:DiEdgeLike[X],W]<:BaseDiGraph[X,Y,Z,W]](
      g: G[String,NL,IdDiEdge[Int,String],EL],
      leftNodeMap: Map[String,String],
      rightNodeMap: Map[String,String]): Unit = {
      val maxEdgeId = (g.edges.map(_.id) + 0).max
      cnt = Counter(maxEdgeId + 1)
      fn1 = leftNodeMap
      fn2 = rightNodeMap
    }
    def left(e1: IdDiEdge[Int,String]) =
      IdDiEdge(cnt.next,fn1(e1.source),fn1(e1.target))
    def right(e2: IdDiEdge[Int,String]) =
      IdDiEdge(cnt.next,fn2(e2.source),fn2(e2.target))
  }

  implicit object StringIdDiEdgeDiGraphBuilder
      extends (() => DiGraph[String,String,IdDiEdge[Int,String],String]) {
    def apply() = DiGraph.empty[String,String,IdDiEdge[Int,String],String]
  }
}

