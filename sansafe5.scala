// Code generated by Isabelle
package tp67

import utilities.Datatype._
// automatic conversion of utilities.Datatype.Int.int to tp67.Int.int
object AutomaticConversion{ 
	implicit def int2int(i:utilities.Datatype.Int.int):Int.int =
			i match {
			case utilities.Datatype.Int.int_of_integer(i)=>Int.int_of_integer(i)
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

def equal_inta(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) == Code_Numeral.integer_of_int(l)

implicit def equal_int: HOL.equal[int] = new HOL.equal[int] {
  val `HOL.equal` = (a: int, b: int) => equal_inta(a, b)
}

def plus_int(k: int, l: int): int =
  int_of_integer(Code_Numeral.integer_of_int(k) +
                   Code_Numeral.integer_of_int(l))

def zero_int: int = int_of_integer(BigInt(0))

def minus_int(k: int, l: int): int =
  int_of_integer(Code_Numeral.integer_of_int(k) -
                   Code_Numeral.integer_of_int(l))

} /* object Int */

object Product_Type {

def equal_boola(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

implicit def equal_bool: HOL.equal[Boolean] = new HOL.equal[Boolean] {
  val `HOL.equal` = (a: Boolean, b: Boolean) => equal_boola(a, b)
}

} /* object Product_Type */

object String {

implicit def equal_char: HOL.equal[Char] = new HOL.equal[Char] {
  val `HOL.equal` = (a: Char, b: Char) => a == b
}

} /* object String */

object Lista {

def equal_list[A : HOL.equal](x0: List[A], x1: List[A]): Boolean = (x0, x1)
  match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) =>
    HOL.eq[A](x21, y21) && equal_list[A](x22, y22)
  case (Nil, Nil) => true
}

} /* object Lista */

object tp67 {

import /*implicits*/ String.equal_char, Product_Type.equal_bool, Int.equal_int

abstract sealed class option[A]
final case class Nonea[A]() extends option[A]
final case class Somea[A](a: A) extends option[A]

def equal_option[A : HOL.equal](x0: option[A], x1: option[A]): Boolean =
  (x0, x1) match {
  case (Nonea(), Somea(a)) => false
  case (Somea(a), Nonea()) => false
  case (Somea(aa), Somea(a)) => HOL.eq[A](aa, a)
  case (Nonea(), Nonea()) => true
}

def equal_expression(x0: expression, x1: expression): Boolean = (x0, x1) match {
  case (Sum(expression1a, expression2a), Sub(expression1, expression2)) => false
  case (Sub(expression1a, expression2a), Sum(expression1, expression2)) => false
  case (Variable(list), Sub(expression1, expression2)) => false
  case (Sub(expression1, expression2), Variable(list)) => false
  case (Variable(list), Sum(expression1, expression2)) => false
  case (Sum(expression1, expression2), Variable(list)) => false
  case (Constant(int), Sub(expression1, expression2)) => false
  case (Sub(expression1, expression2), Constant(int)) => false
  case (Constant(int), Sum(expression1, expression2)) => false
  case (Sum(expression1, expression2), Constant(int)) => false
  case (Constant(int), Variable(list)) => false
  case (Variable(list), Constant(int)) => false
  case (Sub(expression1a, expression2a), Sub(expression1, expression2)) =>
    equal_expression(expression1a, expression1) &&
      equal_expression(expression2a, expression2)
  case (Sum(expression1a, expression2a), Sum(expression1, expression2)) =>
    equal_expression(expression1a, expression1) &&
      equal_expression(expression2a, expression2)
  case (Variable(lista), Variable(list)) => Lista.equal_list[Char](lista, list)
  case (Constant(inta), Constant(int)) => Int.equal_inta(inta, int)
}

def optionOp[A, B](x0: (option[A], (option[A], A => A => B))): option[B] = x0
  match {
  case (Nonea(), (y, f)) => Nonea[B]()
  case (Somea(v), (Nonea(), f)) => Nonea[B]()
  case (Somea(a1), (Somea(a2), f)) => Somea[B]((f(a1))(a2))
}

def noVarEval(x0: expression): option[Int.int] = x0 match {
  case Constant(c) => Somea[Int.int](c)
  case Variable(uu) => Nonea[Int.int]()
  case Sum(e1, e2) =>
    optionOp[Int.int,
              Int.int]((noVarEval(e1),
                         (noVarEval(e2),
                           (a: Int.int) => (b: Int.int) => Int.plus_int(a, b))))
  case Sub(e1, e2) =>
    optionOp[Int.int,
              Int.int]((noVarEval(e1),
                         (noVarEval(e2),
                           (a: Int.int) =>
                             (b: Int.int) => Int.minus_int(a, b))))
}

def noVarEvalCond2(x0: condition): option[Boolean] = x0 match {
  case Eq(c1, c2) =>
    (if (equal_expression(c1, c2)) Somea[Boolean](true)
      else optionOp[Int.int,
                     Boolean]((noVarEval(c1),
                                (noVarEval(c2),
                                  (a: Int.int) =>
                                    (b: Int.int) => Int.equal_inta(a, b)))))
}

def san5(x0: statement): Boolean = x0 match {
  case Exec(e) =>
    (if (equal_option[Int.int](noVarEval(e), Somea[Int.int](Int.zero_int)) ||
           equal_option[Int.int](noVarEval(e), Nonea[Int.int]()))
      false else true)
  case Seq(h, t) => san5(h) && san5(t)
  case If(b, s1, s2) =>
    (if (equal_option[Boolean](noVarEvalCond2(b), Nonea[Boolean]()))
      san5(s1) && san5(s2)
      else (if (equal_option[Boolean](noVarEvalCond2(b), Somea[Boolean](true)))
             san5(s1) else san5(s2)))
  case Aff(v, va) => true
  case Read(v) => true
  case Print(v) => true
  case Skip => true
}

def safe(s: statement): Boolean = san5(s)

} /* object tp67 */