(*
  Statement-only formalization of VERINA corpus artifact verina_basic_47
  (verina__isabelle__verina_basic_47), catalog title "arraySum": an executable
  program sums all entries of a nonempty integer array, together with its
  recursive reference sum, postcondition, and final correctness proposition.
  This file contains no proof.
*)

theory verina_basic_47
  imports Main
begin

definition arraySum_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "arraySum_getBang a i =
    (if i < length a then a ! i else 0)"

definition arraySum_precond :: "int list \<Rightarrow> bool" where
  "arraySum_precond a \<longleftrightarrow> length a > 0"

definition arraySum :: "int list \<Rightarrow> int" where
  "arraySum a = sum_list a"

fun sumTo :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "sumTo a 0 = 0"
| "sumTo a (Suc n) = sumTo a n + arraySum_getBang a n"

definition arraySum_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "arraySum_postcond a result \<longleftrightarrow>
    result - sumTo a (length a) = 0 \<and>
    result \<ge> sumTo a (length a)"

theorem arraySum_spec_satisfied:
  assumes "arraySum_precond a"
  shows "arraySum_postcond a (arraySum a)"
  sorry

end
