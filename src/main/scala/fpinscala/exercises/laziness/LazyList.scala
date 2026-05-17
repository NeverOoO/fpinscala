package fpinscala.exercises.laziness

import fpinscala.exercises.laziness.LazyList.*

enum LazyList[+A]:
  case Empty
  case Cons(h: () => A, t: () => LazyList[A])

  def toList: List[A] = this match {
    case Empty => List.empty
    case Cons(h, t) => h() :: t().toList
  }

  def foldRight[B](z: => B)(f: (A, => B) => B): B = // The arrow `=>` in front of the argument type `B` means that the function `f` takes its second argument by name and may choose not to evaluate it.
    this match
      case Cons(h,t) => f(h(), t().foldRight(z)(f)) // If `f` doesn't evaluate its second argument, the recursion never occurs.
      case _ => z

  def exists(p: A => Boolean): Boolean = 
    foldRight(false)((a, b) => p(a) || b) // Here `b` is the unevaluated recursive step that folds the tail of the lazy list. If `p(a)` returns `true`, `b` will never be evaluated and the computation terminates early.

  @annotation.tailrec
  final def find(f: A => Boolean): Option[A] = this match
    case Empty => None
    case Cons(h, t) => if (f(h())) Some(h()) else t().find(f)

  def take(n: Int): LazyList[A] = this match {
    case Cons(h, t) if n > 1 => cons(h(), t().take(n - 1))
    case Cons(h, _) if n == 1 => cons(h(), Empty)
    case _ => Empty
  }

  def drop(n: Int): LazyList[A] = this match {
    case Cons(_, t) if n > 0 => t().drop(n - 1)
    case _ => this
  }

  def takeWhile(p: A => Boolean): LazyList[A] = this match {
    case Cons(h, t) if p(h()) => cons(h(), t().takeWhile(p))
    case Cons(h, t) => t().takeWhile(p)
    case _ => Empty
  }

  def forAll(p: A => Boolean): Boolean = this match {
    case Cons(h, t) if p(h()) => t().forAll(p)
    case Cons(_, _) => false
    case Empty => true
  }

  def headOption: Option[A] = this match {
    case Cons(h, _) => Some(h())
    case _ => None
  }

  // 5.7 map, filter, append, flatmap using foldRight. Part of the exercise is
  // writing your own function signatures.

  def takeWhileByFold(p: A => Boolean): LazyList[A] =
    foldRight(empty)((a, acc) => if p(a) then cons(a, acc) else Empty)

  def headOptionByFold: Option[A] =
    foldRight(None: Option[A])((a, acc) => Some(a))

  def map[B](f: A => B): LazyList[B] =
    foldRight(empty[B])((a, acc) => cons(f(a), acc))

  def filter(f: A => Boolean): LazyList[A] =
    foldRight(empty[A])((a, acc) => if f(a) then cons(a, acc) else acc)

  def append[A2 >: A](that: => LazyList[A2]): LazyList[A2] =
    foldRight(that)((a, acc) => cons(a, acc))

  def flatMap[B](f: A => LazyList[B]): LazyList[B] =
    foldRight(empty[B])((a, acc) => f(a).append(acc))

  def mapViaUnfold[B](f: A => B): LazyList[B] =
    unfold(this):
      case Cons(h, t) => Some((f(h()), t()))
      case _ => None

  def takeViaUnfold(n: Int): LazyList[A] =
    unfold((n, this)):
      case (idx, Cons(h, t)) if (idx > 0) => Some((h(), (idx - 1, t())))
      case _ => None

  def takeWhileViaUnfold(f: A => Boolean): LazyList[A] =
    unfold(this):
      case Cons(h, t) if f(h()) => Some((h(), t()))
      case _ => None

  def zipAll[B](that: LazyList[B]): LazyList[(Option[A], Option[B])] =
    unfold((this, that)):
      case (Cons(h1, t1), Cons(h2, t2)) => Some((Some(h1()), Some(h2())), (t1(), t2()))
      case (Empty, Cons(h2, t2)) => Some((None, Some(h2())), (Empty, t2()))
      case (Cons(h1, t1), Empty) => Some((Some(h1()), None), (t1(), Empty))
      case (Empty, Empty) => None

  def zipWith[B, C](that: LazyList[B])(f: (A, B) => C): LazyList[C] =
    unfold((this, that)):
      case (Cons(h1, t1), Cons(h2, t2)) => Some((f(h1(), h2())), (t1(), t2()))
      case (_, _) => None

  // special case of `zipWith`
  def zip[B](that: LazyList[B]): LazyList[(A, B)] =
    zipWith(that)((_, _))

  def zipWithAll[B, C](that: LazyList[B])(f: (Option[A], Option[B]) => C): LazyList[C] =
    zipAll(that).map((a, b) => f(a, b))

  def zipAllViaZipWithAll[B](s2: LazyList[B]): LazyList[(Option[A], Option[B])] =
    zipWithAll(s2)((_, _))

  /*
  `s.startsWith(s2)` when corresponding elements of `s` and `s2` are all equal, until the point that `s2` is exhausted. If `s` is exhausted first, or we find an element that doesn't match, we terminate early. Using non-strictness, we can compose these three separate logical steps--the zipping, the termination when the second lazy list is exhausted, and the termination if a nonmatching element is found or the first lazy list is exhausted.
  */
  def startsWith[A](prefix: LazyList[A]): Boolean = (this, prefix) match {
    case (Empty, Cons(h, _)) => false
    case(_, Empty) => true
    case(Cons(h1, t1), Cons(h2, t2)) if h1() == h2() => t1().startsWith(t2())
    case (_, _) => false
  }

  /*
  The last element of `tails` is always the empty `LazyList`, so we handle this as a special case, by appending it to the output.
  */
  def tails: LazyList[LazyList[A]] =
    unfold(this):
      case Empty => None
      case Cons(h, t) => Some((Cons(h, t), t()))
    .append(LazyList(empty))

  def hasSubsequence[A](s: LazyList[A]): Boolean =
    tails.exists(_.startsWith(s))

  /*
  The function can't be implemented using `unfold`, since `unfold` generates elements of the `LazyList` from left to right. It can be implemented using `foldRight` though.

  The implementation is just a `foldRight` that keeps the accumulated value and the lazy list of intermediate results, which we `cons` onto during each iteration. When writing folds, it's common to have more state in the fold than is needed to compute the result. Here, we simply extract the accumulated list once finished.
  */
  def scanRight[B](init: B)(f: (A, => B) => B): LazyList[B] =
    foldRight(init -> LazyList(init)): (a, b0) =>
      // b0 is passed by-name and used in by-name args in f and cons. So use lazy val to ensure only one evaluation...
      lazy val b1 = b0
      val b2 = f(a, b1(0))
      (b2, cons(b2, b1(1)))
    ._2


object LazyList:
  def cons[A](hd: => A, tl: => LazyList[A]): LazyList[A] = 
    lazy val head = hd
    lazy val tail = tl
    Cons(() => head, () => tail)

  def empty[A]: LazyList[A] = Empty

  def apply[A](as: A*): LazyList[A] =
    if as.isEmpty then empty 
    else cons(as.head, apply(as.tail*))

  val ones: LazyList[Int] = LazyList.cons(1, ones)

  def continually[A](a: A): LazyList[A] = LazyList.cons(a, continually(a))

  def from(n: Int): LazyList[Int] = LazyList.cons(n, from(n + 1))

  lazy val fibs: LazyList[Int] =
    def go(curr: Int, next: Int): LazyList[Int] =
      cons(curr, go(next, curr + next))
    go(0,1)

  def unfold[A, S](state: S)(f: S => Option[(A, S)]): LazyList[A] =
    f(state).map((a, s) => cons(a, unfold(s)(f))).getOrElse(empty[A])

  lazy val fibsViaUnfold: LazyList[Int] =
    unfold((0, 1))((curr, next) => Some(curr, (curr, curr + next)))

  def fromViaUnfold(n: Int): LazyList[Int] =
    unfold(n)(n => Some(n, n + 1))

  def continuallyViaUnfold[A](a: A): LazyList[A] = {
//    unfold(a)(n => Some(n, n))
    unfold(())(_ => Some(a, ()))
  }

  lazy val onesViaUnfold: LazyList[Int] =
    unfold(())(_ => Some(1, ()))
