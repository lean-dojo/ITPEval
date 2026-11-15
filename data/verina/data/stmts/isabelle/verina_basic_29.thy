(*
  Statement-only formalization of VERINA corpus artifact verina_basic_29
  (verina__isabelle__verina_basic_29), catalog title "removeElement": an
  executable integer-array program removes the element at a valid natural
  index, preserving the prefix and shifting the suffix one position left,
  together with its precondition, postcondition, and final correctness
  proposition. This file contains no proof.
*)

theory verina_basic_29
  imports Main
begin

definition removeElement_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "removeElement_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition removeElement_precond ::
    "int list \<Rightarrow> nat \<Rightarrow> bool" where
  "removeElement_precond s k \<longleftrightarrow> k < length s"

fun removeElement_eraseIdx ::
    "int list \<Rightarrow> nat \<Rightarrow> int list" where
  "removeElement_eraseIdx [] k = []"
| "removeElement_eraseIdx (x # xs) 0 = xs"
| "removeElement_eraseIdx (x # xs) (Suc k) =
    x # removeElement_eraseIdx xs k"

definition removeElement ::
    "int list \<Rightarrow> nat \<Rightarrow> int list" where
  "removeElement s k = removeElement_eraseIdx s k"

definition removeElement_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> bool" where
  "removeElement_postcond s k result \<longleftrightarrow>
    length result = length s - 1 \<and>
    (\<forall>i. i < k \<longrightarrow>
      removeElement_getBang result i = removeElement_getBang s i) \<and>
    (\<forall>i. i < length result \<longrightarrow> i \<ge> k \<longrightarrow>
      removeElement_getBang result i = removeElement_getBang s (i + 1))"

theorem removeElement_spec_satisfied:
  assumes "removeElement_precond s k"
  shows "removeElement_postcond s k (removeElement s k)"
  sorry

end
