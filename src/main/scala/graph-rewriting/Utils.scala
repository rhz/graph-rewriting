package graph_rewriting

object utils {

  // RHZ: This should definitely create a Stream
  /** Pick an element of each sequence non-deterministically. */
  def cross[A](xss: Seq[Seq[A]], seen: Set[A] = Set[A]())
      : Seq[Seq[A]] = xss match {
    case Seq() => List(List())
    case xs +: xss =>
      for { y <- xs if !seen(y);
            yss <- cross(xss, seen + y)
      } yield (y +: yss)
  }

  // RHZ: I think this shouldn't exist.  It's easier to do
  // val (xs, ys) = xys.unzip; (xs.flatten, ys.flatten)
  /** Concatenate `Seq`s in pairs in the obvious way. */
  def concatPairs[A, B](xys: Iterable[(Set[A], Set[B])])
      : (Set[A], Set[B]) =
    xys.foldRight((Set[A](), Set[B]())) {
      case ((xs, ys), (xss, yss)) => (xs ++: xss, ys ++: yss) }


  /** Implicit class transforming `Function1`s that return `Option`
    * into `PartialFunction`s.
    */
  implicit class UnliftableFunction[A,B](f: A => Option[B]) {

    def unlift = new PartialFunction[A,B] {
      private[this] var tested = false
      private[this] var arg: A = _
      private[this] var ans: Option[B] = None
      private[this] def cache(a: A) {
        if (!tested) {
          tested = true
          arg = a
          ans = f(a)
        } else if (a != arg) {
          arg = a
          ans = f(a)
        }
      }
      def isDefinedAt(a: A) = {
        cache(a)
        ans.isDefined
      }
      def apply(a: A) = {
        cache(a)
        ans.get
      }
    }
  }

  class Counter private (private var i: Int) {
    def apply(): Int = {
      val j = i
      i += 1
      j
    }
  }
  object Counter {
    def apply() = new Counter(0)
    def apply(i: Int) = new Counter(i)
  }
}
