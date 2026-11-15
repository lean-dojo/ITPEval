(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_41,
  catalog title "maxOfThree": an executable nested-comparison program returns
  the maximum of three integers, together with its upper-bound and
  input-membership correctness contract. This file contains no proof.
*)

theory verina_advanced_41
  imports Main
begin

definition maxOfThree_precond ::
    "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "maxOfThree_precond a b c \<longleftrightarrow> True"

definition maxOfThree :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "maxOfThree a b c =
    (if a \<ge> b \<and> a \<ge> c then a
     else if b \<ge> a \<and> b \<ge> c then b
     else c)"

definition maxOfThree_postcond ::
    "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "maxOfThree_postcond a b c result \<longleftrightarrow>
    (result \<ge> a \<and> result \<ge> b \<and> result \<ge> c) \<and>
    (result = a \<or> result = b \<or> result = c)"

theorem maxOfThree_spec_satisfied:
  assumes "maxOfThree_precond a b c"
  shows "maxOfThree_postcond a b c (maxOfThree a b c)"
  sorry

end
