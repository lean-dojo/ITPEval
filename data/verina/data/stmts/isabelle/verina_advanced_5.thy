(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_5,
  catalog title "addTwoNumbers": an executable carry-based addition program
  for nonempty reverse-order decimal digit lists, together with its canonical
  input precondition and numeric and digit-list postcondition. This file
  contains no proof.
*)

theory verina_advanced_5
  imports Main
begin

fun listToNat :: "nat list \<Rightarrow> nat" where
  "listToNat [] = 0"
| "listToNat (d # ds) = d + 10 * listToNat ds"

definition listGetLastBang :: "nat list \<Rightarrow> nat" where
  "listGetLastBang xs = (if xs = [] then 0 else last xs)"

definition addTwoNumbers_precond ::
    "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "addTwoNumbers_precond l1 l2 \<longleftrightarrow>
    length l1 > 0 \<and>
    length l2 > 0 \<and>
    (\<forall>d \<in> set l1. d < 10) \<and>
    (\<forall>d \<in> set l2. d < 10) \<and>
    (listGetLastBang l1 \<noteq> 0 \<or> l1 = [0]) \<and>
    (listGetLastBang l2 \<noteq> 0 \<or> l2 = [0])"

fun addTwoNumbers_aux ::
    "nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "addTwoNumbers_aux [] [] carry =
    (if carry = 0 then [] else [carry])"
| "addTwoNumbers_aux (h1 # t1) [] carry =
    (let sum = h1 + carry
     in (sum mod 10) # addTwoNumbers_aux t1 [] (sum div 10))"
| "addTwoNumbers_aux [] (h2 # t2) carry =
    (let sum = h2 + carry
     in (sum mod 10) # addTwoNumbers_aux [] t2 (sum div 10))"
| "addTwoNumbers_aux (h1 # t1) (h2 # t2) carry =
    (let sum = h1 + h2 + carry
     in (sum mod 10) # addTwoNumbers_aux t1 t2 (sum div 10))"

definition addTwoNumbers ::
    "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "addTwoNumbers l1 l2 = addTwoNumbers_aux l1 l2 0"

definition addTwoNumbers_postcond ::
    "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "addTwoNumbers_postcond l1 l2 result \<longleftrightarrow>
    listToNat result = listToNat l1 + listToNat l2 \<and>
    (\<forall>d \<in> set result. d < 10) \<and>
    (listGetLastBang result \<noteq> 0 \<or>
      (l1 = [0] \<and> l2 = [0] \<and> result = [0]))"

theorem addTwoNumbers_spec_satisfied:
  assumes "addTwoNumbers_precond l1 l2"
  shows "addTwoNumbers_postcond l1 l2 (addTwoNumbers l1 l2)"
  sorry

end
