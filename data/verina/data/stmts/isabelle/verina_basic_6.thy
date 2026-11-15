(*
  Statement-only formalization of VERINA corpus artifact verina_basic_6
  (verina__isabelle__verina_basic_6), catalog title "minOfThree": an
  executable integer comparison program returns the minimum of three inputs,
  together with its unconditional precondition, exact minimum postcondition,
  and final correctness proposition. This file contains no proof.
*)

theory verina_basic_6
  imports Main
begin

definition minOfThree_precond ::
    "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "minOfThree_precond a b c \<longleftrightarrow> True"

definition minOfThree ::
    "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "minOfThree a b c =
    (if a \<le> b \<and> a \<le> c then a
     else if b \<le> a \<and> b \<le> c then b
     else c)"

definition minOfThree_postcond ::
    "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "minOfThree_postcond a b c result \<longleftrightarrow>
    (result \<le> a \<and> result \<le> b \<and> result \<le> c) \<and>
    (result = a \<or> result = b \<or> result = c)"

theorem minOfThree_spec_satisfied:
  assumes "minOfThree_precond a b c"
  shows "minOfThree_postcond a b c (minOfThree a b c)"
  sorry

end
