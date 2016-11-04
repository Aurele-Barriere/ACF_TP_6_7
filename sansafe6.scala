// Code generated by Isabelle
package tp67

import utilities.Datatype._
// automatic conversion of utilities.Datatype.Int.int to tp67.Int.int
object AutomaticConversion{ 
	implicit def int2int(i:utilities.Datatype.Int.int):tp67.Int.int =
			i match {
			case utilities.Datatype.Int.int_of_integer(i)=>tp67.Int.int_of_integer(i)
	}
}
import AutomaticConversion._


object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Code_Numeral {

def integer_of_int(x0: Int.int): BigInt = x0 match {
  case Int.int_of_integer(k) => k
}

} /* object Code_Numeral */

object Int {

abstract sealed class int
final case class int_of_integer(a: BigInt) extends int

def plus_int(k: int, l: int): int =
  int_of_integer(Code_Numeral.integer_of_int(k) +
                   Code_Numeral.integer_of_int(l))

def zero_int: int = int_of_integer(BigInt(0))

def equal_int(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) == Code_Numeral.integer_of_int(l)

def minus_int(k: int, l: int): int =
  int_of_integer(Code_Numeral.integer_of_int(k) -
                   Code_Numeral.integer_of_int(l))

def uminus_int(k: int): int =
  int_of_integer((- (Code_Numeral.integer_of_int(k))))

} /* object Int */

object Num {

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

} /* object Num */

object String {

implicit def equal_char: HOL.equal[Char] = new HOL.equal[Char] {
  val `HOL.equal` = (a: Char, b: Char) => a == b
}

} /* object String */

object Lista {

def equal_lista[A : HOL.equal](x0: List[A], x1: List[A]): Boolean = (x0, x1)
  match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) =>
    HOL.eq[A](x21, y21) && equal_lista[A](x22, y22)
  case (Nil, Nil) => true
}

implicit def equal_list[A : HOL.equal]: HOL.equal[List[A]] = new
  HOL.equal[List[A]] {
  val `HOL.equal` = (a: List[A], b: List[A]) => equal_lista[A](a, b)
}

} /* object Lista */

object tp67 {

import /*implicits*/ String.equal_char, Lista.equal_list

abstract sealed class abstracta
final case class Any() extends abstracta
final case class Defined(a: Int.int) extends abstracta

def equal_abstracta(x0: abstracta, x1: abstracta): Boolean = (x0, x1) match {
  case (Any(), Defined(int)) => false
  case (Defined(int), Any()) => false
  case (Defined(inta), Defined(int)) => Int.equal_int(inta, int)
  case (Any(), Any()) => true
}

implicit def equal_abstract: HOL.equal[abstracta] = new HOL.equal[abstracta] {
  val `HOL.equal` = (a: abstracta, b: abstracta) => equal_abstracta(a, b)
}

abstract sealed class option[A]
final case class Nonea[A]() extends option[A]
final case class Somea[A](a: A) extends option[A]

abstract sealed class abs_bool
final case class ATrue() extends abs_bool
final case class AFalse() extends abs_bool
final case class AAny() extends abs_bool

def equal_abs_bool(x0: abs_bool, x1: abs_bool): Boolean = (x0, x1) match {
  case (AFalse(), AAny()) => false
  case (AAny(), AFalse()) => false
  case (ATrue(), AAny()) => false
  case (AAny(), ATrue()) => false
  case (ATrue(), AFalse()) => false
  case (AFalse(), ATrue()) => false
  case (AAny(), AAny()) => true
  case (AFalse(), AFalse()) => true
  case (ATrue(), ATrue()) => true
}

def equal_option[A : HOL.equal](x0: option[A], x1: option[A]): Boolean =
  (x0, x1) match {
  case (Nonea(), Somea(a)) => false
  case (Somea(a), Nonea()) => false
  case (Somea(aa), Somea(a)) => HOL.eq[A](aa, a)
  case (Nonea(), Nonea()) => true
}

def allAny(x0: List[(List[Char], abstracta)]): List[(List[Char], abstracta)] =
  x0 match {
  case Nil => Nil
  case (s, a) :: t => (s, Any()) :: allAny(t)
}

def assoc[A : HOL.equal, B](uu: A, x1: List[(A, B)]): option[B] = (uu, x1) match
  {
  case (uu, Nil) => Nonea[B]()
  case (x1, (x, y) :: xs) =>
    (if (HOL.eq[A](x, x1)) Somea[B](y) else assoc[A, B](x1, xs))
}

def BothTables(x0: List[(List[Char], abstracta)],
                t2: List[(List[Char], abstracta)]):
      List[(List[Char], abstracta)]
  =
  (x0, t2) match {
  case (Nil, t2) => allAny(t2)
  case ((s, a) :: t, t2) =>
    {
      val r: option[abstracta] = assoc[List[Char], abstracta](s, t2);
      (if (equal_option[abstracta](r, Somea[abstracta](a)))
        (s, a) :: BothTables(t, t2) else (s, Any()) :: BothTables(t, t2))
    }
}

def abs_plus(x0: abstracta, uu: abstracta): abstracta = (x0, uu) match {
  case (Any(), uu) => Any()
  case (Defined(v), Any()) => Any()
  case (Defined(n1), Defined(n2)) => Defined(Int.plus_int(n1, n2))
}

def abs_sub(x0: abstracta, uu: abstracta): abstracta = (x0, uu) match {
  case (Any(), uu) => Any()
  case (Defined(v), Any()) => Any()
  case (Defined(n1), Defined(n2)) => Defined(Int.minus_int(n1, n2))
}

def AevalE(x0: expression, e: List[(List[Char], abstracta)]): abstracta =
  (x0, e) match {
  case (Constant(s), e) => Defined(s)
  case (Variable(s), e) =>
    (assoc[List[Char], abstracta](s, e) match {
       case Nonea() => Defined(Int.uminus_int(Int.int_of_integer(BigInt(1))))
       case Somea(y) => y
     })
  case (Sum(e1, e2), e) => abs_plus(AevalE(e1, e), AevalE(e2, e))
  case (Sub(e1, e2), e) => abs_sub(AevalE(e1, e), AevalE(e2, e))
}

def abs_eq(x0: abstracta, uu: abstracta): abs_bool = (x0, uu) match {
  case (Any(), uu) => AAny()
  case (Defined(v), Any()) => AAny()
  case (Defined(a1), Defined(a2)) =>
    (if (Int.equal_int(a1, a2)) ATrue() else AFalse())
}

def AevalC(x0: condition, t: List[(List[Char], abstracta)]): abs_bool = (x0, t)
  match {
  case (Eq(e1, e2), t) => abs_eq(AevalE(e1, t), AevalE(e2, t))
}

def AevalS(xa0: statement, x: (List[(List[Char], abstracta)], Boolean)):
      (List[(List[Char], abstracta)], Boolean)
  =
  (xa0, x) match {
  case (Skip, x) => x
  case (Aff(s, e), (t, b)) => ((s, AevalE(e, t)) :: t, b)
  case (If(c, s1, s2), (t, b)) =>
    {
      val r: abs_bool = AevalC(c, t);
      (if (equal_abs_bool(r, ATrue())) AevalS(s1, (t, b))
        else (if (equal_abs_bool(r, AFalse())) AevalS(s2, (t, b))
               else {
                      val (t1, b1): (List[(List[Char], abstracta)], Boolean) =
                        AevalS(s1, (t, b))
                      val (t2, b2): (List[(List[Char], abstracta)], Boolean) =
                        AevalS(s2, (t, b))
                      val b3: Boolean = b1 && b2
                      val t3: List[(List[Char], abstracta)] =
                        BothTables(t1, t2);
                      (t3, b3)
                    }))
    }
  case (Seq(s1, s2), (t, b)) =>
    {
      val (t2, b2): (List[(List[Char], abstracta)], Boolean) =
        AevalS(s1, (t, b));
      AevalS(s2, (t2, b2))
    }
  case (Read(s), (t, b)) => ((s, Any()) :: t, b)
  case (Print(e), (t, b)) => (t, b)
  case (Exec(e), (t, b)) =>
    {
      val r: abstracta = AevalE(e, t);
      (if (equal_abstracta(r, Any()) ||
             equal_abstracta(r, Defined(Int.zero_int)))
        (t, false) else (t, b))
    }
}

def san6(s: statement): Boolean =
  {
    val (_, b): (List[(List[Char], abstracta)], Boolean) =
      AevalS(s, (Nil, true));
    b
  }

def safe(s: statement): Boolean = san6(s)

} /* object tp67 */