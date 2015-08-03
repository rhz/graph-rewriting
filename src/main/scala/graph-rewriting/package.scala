package object graph_rewriting {

  import utils.Counter

  def next(xs: Traversable[Int]) = if (xs.isEmpty) 0 else (xs.max + 1)

  // -- Nodes --

  implicit def newIntNode[G<:BaseGraph[Int,_,_,_]](g: G): Int =
    next(g.nodes)
  implicit def newStringNode[G<:BaseGraph[String,_,_,_]](g: G)
      : String = {
    val id = util.Random.nextString(10)
    if (g.nodes contains id) newStringNode(g) else id
  }


  // -- Edges --

  final implicit class DiEdgeConst[N](n1: N) {
    def ~> (n2: N) = DiEdge(n1,n2)
  }
  final implicit class IdDiEdgeConst[N](n1: N) {
    def ~~> (n2: N) = IdDiEdge(Counter.next,n1,n2)
  }
  implicit def newIdDiEdge[N,
    G<:BaseDiGraph[N,_,IdDiEdge[Int,N],_]](g: G, u: N, v: N) =
    new IdDiEdge(next(g(u).edgesTo(v).map(_.id)), u, v)


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

  implicit def graphToMn[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    g: G[N,NL,E,EL]): Mn[N,NL,E,EL,G] = Mn(g)
  implicit def graphToPn[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    g: G[N,NL,E,EL]): Pn[N,NL,E,EL,G] = Pn[N,NL,E,EL,G](Mn(g))
  implicit def mnToPn[N,NL,E<:DiEdgeLike[N],EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    m: Mn[N,NL,E,EL,G]) = Pn[N,NL,E,EL,G](m)
  // Rates don't have required type information
  // implicit def nameToMn(name: String) = Mn(name)
  // implicit def nameToPn(name: String) = Pn(Mn(name))
  // implicit def rateToMn(k: Rate) = Mn(k)
  // implicit def rateToPn(k: Rate) = Pn(Mn(k))
  // implicit def rateMnToMn(rm: RateMn) = Mn(rm)
  // implicit def rateMnToPn(rm: RateMn) = Pn(Mn(rm))
  // implicit def ratePnToMn(rp: RatePn) = Mn(rp)
  // implicit def ratePnToPn(rp: RatePn) = Pn(Mn(rp))


  // -- Graph --
  implicit def withLabel[T,U](x: (T,U)) = (x._1,Some(x._2))
  implicit def withoutLabel[T,U](x: T): (T,Option[U])  = (x,None)
  implicit def toSome[T](x: T) = Some(x)


  // -- Unify nodes and edges --
  implicit object StringNodeUnifier
      extends Unifier[String,String,String] {
    def unify(u: String, v: String) = s"($u,$v)"
    def left(u: String) = s"($u,)"
    def right(u: String) = s"(,$u)"
  }

  implicit def idDiEdgeUnifier[N,NL,EL,
    G[X,Y,Z<:DiEdgeLike[X],W] <: BaseDiGraph[X,Y,Z,W]](
    g: G[N,NL,IdDiEdge[Int,N],EL],
    leftNodeMap: Map[N,N],
    rightNodeMap: Map[N,N]) = {
    val maxEdgeId = (g.edges.map(_.id) + -1).max
    val cnt = Counter(maxEdgeId + 1)
    new Unifier[IdDiEdge[Int,N],IdDiEdge[Int,N],IdDiEdge[Int,N]] {
      def unify(e1: IdDiEdge[Int,N], e2: IdDiEdge[Int,N]) = {
        require(leftNodeMap(e1.source) == rightNodeMap(e2.source),
          s"edges $e1 and $e2 can't be unified: sources differ")
        require(leftNodeMap(e1.target) == rightNodeMap(e2.target),
          s"edges $e1 and $e2 can't be unified: targets differ")
        IdDiEdge(cnt.next,leftNodeMap(e1.source),leftNodeMap(e1.target))
      }
      def left(e1: IdDiEdge[Int,N]) =
        IdDiEdge(cnt.next,leftNodeMap(e1.source),leftNodeMap(e1.target))
      def right(e2: IdDiEdge[Int,N]) =
        IdDiEdge(cnt.next,rightNodeMap(e2.source),rightNodeMap(e2.target))
    }
  }
}

