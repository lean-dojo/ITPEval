(*
  Statement-only formalization of VERINA corpus artifact verina_basic_60
  (verina__isabelle__verina_basic_60), catalog title "FindEvenNumbers": an
  executable integer-array loop retains exactly the even entries in input
  order, together with its unconditional precondition, all-even,
  order-preserving sublist and cardinality postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_60
  imports Main
begin

definition isEven :: "int \<Rightarrow> bool" where
  "isEven n = (n mod 2 = 0)"

definition FindEvenNumbers_precond :: "int list \<Rightarrow> bool" where
  "FindEvenNumbers_precond arr \<longleftrightarrow> True"

fun FindEvenNumbers_loop ::
    "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "FindEvenNumbers_loop [] acc = acc"
| "FindEvenNumbers_loop (x # xs) acc =
    FindEvenNumbers_loop xs
      (if isEven x then acc @ [x] else acc)"

definition FindEvenNumbers :: "int list \<Rightarrow> int list" where
  "FindEvenNumbers arr = FindEvenNumbers_loop arr []"

inductive FindEvenNumbers_sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  FindEvenNumbers_sublist_nil:
    "FindEvenNumbers_sublist [] []"
| FindEvenNumbers_sublist_cons:
    "FindEvenNumbers_sublist xs ys \<Longrightarrow>
      FindEvenNumbers_sublist (x # xs) (x # ys)"
| FindEvenNumbers_sublist_cons_right:
    "FindEvenNumbers_sublist xs ys \<Longrightarrow>
      FindEvenNumbers_sublist xs (y # ys)"

definition FindEvenNumbers_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "FindEvenNumbers_postcond arr result \<longleftrightarrow>
    list_all isEven result \<and>
    FindEvenNumbers_sublist result arr \<and>
    length result = length (filter isEven arr)"

theorem FindEvenNumbers_spec_satisfied:
  assumes "FindEvenNumbers_precond arr"
  shows
    "FindEvenNumbers_postcond arr (FindEvenNumbers arr)"
  sorry

end
