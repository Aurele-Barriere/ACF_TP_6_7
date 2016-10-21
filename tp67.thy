theory tp67
imports Main   "~~/src/HOL/Library/Code_Target_Int" "~~/src/HOL/Library/Code_Char" 
begin

(* Types des expressions, conditions et programmes (statement) *)
datatype expression= Constant int | Variable string | Sum expression expression | Sub expression expression

datatype condition= Eq expression expression

datatype statement= Seq statement statement | 
                    Aff string expression | 
                    Read string | 
                    Print expression | 
                    Exec expression | 
                    If condition statement statement |
                    Skip
(* Un exemple d'expression *)

(* expr1= (x-10) *)
definition "expr1= (Sub (Variable ''x'') (Constant 10))"


(* Des exemples de programmes *)

(* p1= exec(0) *)
definition "p1= Exec (Constant 0)"

(* p2= {
        print(10)
        exec(0+0)
       }
*)

definition "p2= (Seq (Print (Constant 10)) (Exec (Sum (Constant 0) (Constant 0))))"

(* p3= {
         x:=0
         exec(x)
       }
*)

definition "p3= (Seq (Aff ''x'' (Constant 0)) (Exec (Variable ''x'')))"

(* p4= {
         read(x)
         print(x+1)
       }
*)
definition "p4= (Seq (Read ''x'') (Print (Sum (Variable ''x'') (Constant 1))))"


(* Le type des evenements soit X: execute, soit P: print *)
datatype event= X int | P int

(* les flux de sortie, d'entree et les tables de symboles *)

type_synonym outchan= "event list"
definition "el1= [X 1, P 10, X 0, P 20]"                   (* Un exemple de flux de sortie *)

type_synonym inchan= "int list"           
definition "il1= [1,-2,10]"                                (* Un exemple de flux d'entree [1,-2,10]              *)

type_synonym symTable= "(string * int) list"
definition "(st1::symTable)= [(''x'',10),(''y'',12)]"      (* Un exemple de table de symbole *)


(* La fonction (partielle) de recherche dans une liste de couple, par exemple une table de symbole *)
datatype 'a option= None | Some 'a

fun assoc:: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b option"
where
"assoc _ [] = None" |
"assoc x1 ((x,y)#xs)= (if x=x1 then Some(y) else (assoc x1 xs))"

(* Exemples de recherche dans une table de symboles *)

value "assoc ''x'' st1"     (* quand la variable est dans la table st1 *)
value "assoc ''z'' st1"     (* quand la variable n'est pas dans la table st1 *)


(* Evaluation des expressions par rapport a une table de symboles *)
fun evalE:: "expression \<Rightarrow> symTable \<Rightarrow> int"
where
"evalE (Constant s) e = s" |
"evalE (Variable s) e= (case (assoc s e) of None \<Rightarrow> -1 | Some(y) \<Rightarrow> y)" |
"evalE (Sum e1 e2) e= ((evalE e1 e) + (evalE e2 e))" |
"evalE (Sub e1 e2) e= ((evalE e1 e) - (evalE e2 e))" 

(* Exemple d'évaluation d'expression *)

value "evalE expr1 st1"

(* Evaluation des conditions par rapport a une table de symboles *)
fun evalC:: "condition \<Rightarrow> symTable \<Rightarrow> bool"
where
"evalC (Eq e1 e2) t= ((evalE e1 t) = (evalE e2 t))"

(* Evaluation d'un programme par rapport a une table des symboles, a un flux d'entree et un flux de sortie. 
   Rend un triplet: nouvelle table des symboles, nouveaux flux d'entree et sortie *)
fun evalS:: "statement \<Rightarrow> (symTable * inchan * outchan) \<Rightarrow> (symTable * inchan * outchan)"
where
"evalS Skip x=x" |
"evalS (Aff s e)  (t,inch,outch)=  (((s,(evalE e t))#t),inch,outch)" |
"evalS (If c s1 s2)  (t,inch,outch)=  (if (evalC c t) then (evalS s1 (t,inch,outch)) else (evalS s2 (t,inch,outch)))" |
"evalS (Seq s1 s2) (t,inch,outch)= 
    (let (t2,inch2,outch2)= (evalS s1 (t,inch,outch)) in
        evalS s2 (t2,inch2,outch2))" |
"evalS (Read _) (t,[],outch)= (t,[],outch)" |
"evalS (Read s) (t,(x#xs),outch)= (((s,x)#t),xs,outch)" |
"evalS (Print e) (t,inch,outch)= (t,inch,((P (evalE e t))#outch))" |
"evalS (Exec e) (t,inch,outch)= 
  (let res= evalE e t in
   (t,inch,((X res)#outch)))"



(* Exemples d'évaluation de programmes *)
(* Les programmes p1, p2, p3, p4 ont été définis plus haut *)
(* p1= exec(0) *)

value "evalS p1 ([],[],[])"

(* ------------------------------------ *)
(* p2= {
        print(10)
        exec(0+0)
       }
*)

value "evalS p2 ([],[],[])"

(* ------------------------------------ *)
(* p3= {
         x:=0
         exec(x)
       }
*)

value "evalS p3 ([],[],[])"

(* ------------------------------------ *)
(* p4= {
         read(x)
         print(x+1)
       }
*)

value "evalS p4 ([],[10],[])"


definition "bad1= (Exec (Constant 0))"
definition "bad2= (Exec (Sub (Constant 2) (Constant 2)))"
definition "bad3= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x'')) (Exec (Sub (Variable ''x'') (Constant 1)))))"
definition "bad4= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) Skip (Aff ''y'' (Constant 1))) (Exec (Sum (Variable ''y'') (Constant 1)))))"
definition "bad5= (Seq (Read ''x'') (Seq (Aff ''y'' (Sum (Variable ''x'') (Constant 2))) (Seq (If (Eq (Variable ''x'') (Sub (Constant 0) (Constant 1))) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x'')))) (Seq (Aff ''x'' (Sub (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x''))))) (Exec (Variable ''y'')))))"
definition "bad6= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 1)) (Aff ''z'' (Constant 0))) (Exec (Variable ''z''))))"
definition "bad7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 1))) (Exec (Variable ''z''))))"
definition "bad8= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Variable ''x'') (Variable ''y'')) (Exec (Constant 1)) (Exec (Constant 0)))))"
definition "ok0= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Print (Sum (Variable ''y'') (Variable ''x'')))
(Print (Variable ''x''))
) (Print (Variable ''y''))
) (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 2)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 3)) (Seq (Print (Variable ''x''))
 (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Aff ''z'' (Sum (Variable ''x'') (Variable ''x''))) (Aff ''z'' (Sub (Variable ''x'') (Variable ''y'')))) (Print (Variable ''z''))
)))))))))))"
definition "ok1= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Sum (Variable ''x'') (Variable ''x'')))
 (Seq (Exec (Constant 10)) (Seq (Read ''y'') (If (Eq (Variable ''y'') (Constant 0)) (Exec (Constant 1)) (Exec (Constant 2)))))))"
definition "ok2= (Exec (Variable ''y''))"
definition "ok3= (Seq (Read ''x'') (Exec (Sum (Variable ''y'') (Constant 2))))"
definition "ok4= (Seq (Aff ''x'' (Constant 0)) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 20))) (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 4))) (Seq (Exec (Variable ''z'')) (Exec (Variable ''x''))))))"
definition "ok5= (Seq (Read ''x'') (Seq (Aff ''x'' (Constant 4)) (Exec (Variable ''x''))))"
definition "ok6= (Seq (If (Eq (Constant 1) (Constant 2)) (Aff ''x'' (Constant 0)) (Aff ''x'' (Constant 1))) (Exec (Variable ''x'')))"
definition "ok7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (If (Eq (Variable ''x'') (Constant 4)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 1)))) (Exec (Variable ''x''))))"
definition "ok8= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 2))) (Exec (Sub (Variable ''x'') (Constant 3)))))"
definition "ok9= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Sum (Variable ''y'') (Sum (Variable ''y'') (Variable ''x''))))))))"
definition "ok10= (Seq (Read ''x'') (If (Eq (Variable ''x'') (Constant 0)) (Exec (Constant 1)) (Exec (Variable ''x''))))"
definition "ok11= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Sum (Variable ''x'') (Constant 1))) Skip) (Exec (Variable ''x''))))"
definition "ok12= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''z'') (If (Eq (Variable ''z'') (Constant 0)) (Exec (Variable ''y'')) (Exec (Variable ''z'')))))"
definition "ok13= (Seq (Aff ''z'' (Constant 4)) (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (Aff ''x'' (Sum (Variable ''x'') (Sum (Variable ''z'') (Variable ''x'')))) (Seq (Aff ''z'' (Sum (Variable ''z'') (Variable ''x''))) (Seq (If (Eq (Variable ''y'') (Constant 1)) (Aff ''x'' (Sub (Variable ''x'') (Variable ''y''))) Skip) (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Aff ''y'' (Sum (Variable ''y'') (Constant 1))) (Exec (Variable ''x''))) Skip) (Exec (Variable ''y'')))))))))"
definition "ok14= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Variable ''y''))))))"


(* Le TP commence ici! *)

fun inlist::"'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
"inlist _ [] = False" |
"inlist x (h#t) = (if (x=h) then True else inlist x t)"

value "inlist 3 [(1::nat),2,3]"
value "inlist 0 [(1::nat),1,1]"
value "inlist 0 []"

fun BAD:: "(symTable * inchan * outchan) \<Rightarrow> bool"
where
"BAD (_,_,outl) = (inlist (X 0) outl)"



value"BAD(evalS p1 ([],[],[]))"
value"BAD(evalS p2 ([],[],[]))"
value"BAD(evalS p3 ([],[],[]))"
value"BAD(evalS p4 ([],[0],[]))"
value"BAD(evalS bad1 ([],[],[]))"
value"BAD(evalS ok2 ([],[],[]))"

fun san1::"statement \<Rightarrow> bool"
where
"san1 (Exec _) = False" |
"san1 (Seq h t) = (san1 h \<and> san1 t)" |
"san1 (If b s1 s2) = (san1 s1 \<and> san1 s2)" |
"san1 _ = True"

value"san1 p4"
value"san1 ok2" 
value"san1 bad5"

fun san2::"statement \<Rightarrow> bool"
where
"san2 (Exec (Constant c)) = (if (c=0) then False else True)" |
"san2 (Exec _) = False" |
"san2 (Seq h t) = (san2 h \<and> san2 t)" |
"san2 (If b s1 s2) = (san2 s1 \<and> san2 s2)" |
"san2 _ = True"

value"san2 p4"
value"san2 ok2" 
value"san2 bad5"
definition "p5= Exec (Constant 42)"
value"san2 p5"


fun optionOp::"('a option * 'a option * ('a \<Rightarrow> 'a \<Rightarrow> 'b)) \<Rightarrow> 'b option"
where
"optionOp (None, y, f) = None" |
"optionOp (x, None, f) = None" |
"optionOp ((Some a1), (Some a2), f) = (Some (f a1 a2))" 

fun noVarEval::"expression \<Rightarrow> int option"
where
"noVarEval (Constant c) = (Some c)" |
"noVarEval (Variable _) = None" |
"noVarEval (Sum e1 e2) = (optionOp ((noVarEval e1), (noVarEval e2), (\<lambda> a b . a + b)))" |
"noVarEval (Sub e1 e2) = (optionOp ((noVarEval e1), (noVarEval e2), (\<lambda> a b . a - b)))"

fun san3::"statement \<Rightarrow> bool"
where
"san3 (Exec e) = (if (noVarEval(e) = Some 0 \<or> noVarEval(e) = None) then False else True)" |
"san3 (Seq h t) = (san3 h \<and> san3 t)" |
"san3 (If b s1 s2) = (san3 s1 \<and> san3 s2)" |
"san3 _ = True"




value"san3 p4"
value"san3 ok2" 
value"san3 bad2"
definition "p6= Exec (Sub (Constant 3) (Constant 1) ) "
value"san3 p5"
value"san2 p6"
value"san3 p6"



fun noVarEvalCond::"condition \<Rightarrow> bool option"
where
"noVarEvalCond (Eq c1 c2) = (optionOp ((noVarEval c1), (noVarEval c2), (\<lambda> a b . a = b)))" 

fun san4::"statement \<Rightarrow> bool"
where
"san4 (Exec e) = (if (noVarEval(e) = Some 0 \<or> noVarEval(e) = None) then False else True)" |
"san4 (Seq h t) = (san4 h \<and> san4 t)" |
"san4 (If b s1 s2) = (if noVarEvalCond(b) = None then (san4 s1 \<and> san4 s2) else (if noVarEvalCond(b) = Some True then san4 s1 else san4 s2))" |
"san4 _ = True"







fun noVarEvalCond2::"condition \<Rightarrow> bool option"
where
"noVarEvalCond2 (Eq c1 c2) = (if c1 = c2 then Some True else (optionOp ((noVarEval c1), (noVarEval c2), (\<lambda> a b . a = b))))" 

fun san5::"statement \<Rightarrow> bool"
where
"san5 (Exec e) = (if (noVarEval(e) = Some 0 \<or> noVarEval(e) = None) then False else True)" |
"san5 (Seq h t) = (san5 h \<and> san5 t)" |
"san5 (If b s1 s2) = (if noVarEvalCond2(b) = None then (san5 s1 \<and> san5 s2) else (if noVarEvalCond2(b) = Some True then san5 s1 else san5 s2))" |
"san5 _ = True"


fun safe::"statement \<Rightarrow> bool"
where
"safe s = san5 s"




lemma correct: "safe p \<longrightarrow> ( \<forall> inlist. ~BAD (evalS p ([], inlist, [])))"  
nitpick
sorry

lemma complete:  "( \<forall> inlist. ~BAD (evalS p ([], inlist, []))) \<longrightarrow> safe p"
nitpick
oops

(* ----- Restriction de l'export Scala (Isabelle 2014) -------*)
(* ! ! !  NE PAS MODIFIER ! ! ! *)
(* Suppression de l'export des abstract datatypes (Isabelle 2014) *)

code_reserved Scala
  expression condition statement 
code_printing
  type_constructor expression \<rightharpoonup> (Scala) "expression"
  | constant Constant \<rightharpoonup> (Scala) "Constant"
  | constant Variable \<rightharpoonup> (Scala) "Variable"
  | constant Sum \<rightharpoonup> (Scala) "Sum"
  | constant Sub \<rightharpoonup> (Scala) "Sub"  

  | type_constructor condition \<rightharpoonup> (Scala) "condition"
  | constant Eq \<rightharpoonup> (Scala) "Eq"

  | type_constructor statement \<rightharpoonup> (Scala) "statement"
  | constant Seq \<rightharpoonup> (Scala) "Seq"
  | constant Aff \<rightharpoonup> (Scala) "Aff"
  | constant Read \<rightharpoonup> (Scala) "Read"
  | constant Print \<rightharpoonup> (Scala) "Print"
  | constant Exec \<rightharpoonup> (Scala) "Exec"
  | constant If \<rightharpoonup> (Scala) "If"
  | constant Skip \<rightharpoonup> (Scala) "Skip"
  | code_module "" \<rightharpoonup> (Scala) 

{*// Code generated by Isabelle
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
*}


(* Directive pour l'exportation de l'analyseur *)
export_code safe in Scala 
 file "~/workspace/TP67/src/tp67/san.scala"   (* à adapter en fonction du chemin de votre projet TP67 *)



end
