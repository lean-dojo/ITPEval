(*
  Statement-only formalization of VERINA corpus artifact verina_basic_85
  (verina__isabelle__verina_basic_85), catalog title "reverse": an executable
  integer-array program reverses its input by swapping mirrored entries,
  together with its unconditional precondition, reversed-index postcondition,
  and final correctness proposition. This file contains no proof.
*)

theory verina_basic_85
  imports Main
begin

definition reverse_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "reverse_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition reverse_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "reverse_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

definition reverse_precond :: "int list \<Rightarrow> bool" where
  "reverse_precond a \<longleftrightarrow> True"

partial_function (tailrec) reverse_core ::
    "int list \<Rightarrow> nat \<Rightarrow> int list" where
  "reverse_core arr i =
    (if i < length arr div 2 then
       let j = length arr - 1 - i;
           temp = reverse_getBang arr i;
           arr1 = reverse_setBang arr i (reverse_getBang arr j);
           arr2 = reverse_setBang arr1 j temp
       in reverse_core arr2 (i + 1)
     else arr)"

definition reverse :: "int list \<Rightarrow> int list" where
  "reverse a = reverse_core a 0"

definition reverse_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "reverse_postcond a result \<longleftrightarrow>
    length result = length a \<and>
    (\<forall>i. i < length a \<longrightarrow>
      reverse_getBang result i =
        reverse_getBang a (length a - 1 - i))"

theorem reverse_spec_satisfied:
  fixes a :: "int list"
  assumes "reverse_precond a"
  shows "reverse_postcond a (reverse a)"
  sorry

end
