(*
  Statement-only formalization of VERINA corpus artifact verina_basic_4
  (verina__isabelle__verina_basic_4), catalog title "kthElement": an
  executable integer-array program returns the element at the valid one-based
  position k, together with its precondition, membership-and-index
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_4
  imports Main
begin

definition kthElement_precond :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
  "kthElement_precond arr k \<longleftrightarrow>
    1 \<le> k \<and> k \<le> length arr"

fun kthElement_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "kthElement_getBang [] i = 0"
| "kthElement_getBang (x # xs) 0 = x"
| "kthElement_getBang (x # xs) (Suc i) = kthElement_getBang xs i"

definition kthElement :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "kthElement arr k = kthElement_getBang arr (k - 1)"

definition kthElement_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "kthElement_postcond arr k result \<longleftrightarrow>
    list_ex
      (\<lambda>x. x = result \<and> x = kthElement_getBang arr (k - 1))
      arr"

theorem kthElement_spec_satisfied:
  assumes "kthElement_precond arr k"
  shows "kthElement_postcond arr k (kthElement arr k)"
  sorry

end
