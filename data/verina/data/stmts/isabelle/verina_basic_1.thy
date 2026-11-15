(*
  Statement-only formalization of VERINA corpus artifact verina_basic_1,
  catalog title "hasOppositeSign": an executable integer program returns true
  exactly when its two inputs have opposite nonzero signs, together with its
  trivial precondition and correctness contract. This file contains no proof.
*)

theory verina_basic_1
  imports Main
begin

definition hasOppositeSign_precond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "hasOppositeSign_precond a b \<longleftrightarrow> True"

definition hasOppositeSign :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "hasOppositeSign a b = (a * b < 0)"

definition hasOppositeSign_postcond ::
    "int \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> bool" where
  "hasOppositeSign_postcond a b result \<longleftrightarrow>
    ((((a < 0 \<and> b > 0) \<or> (a > 0 \<and> b < 0))
       \<longrightarrow> result) \<and>
     (\<not> ((a < 0 \<and> b > 0) \<or> (a > 0 \<and> b < 0))
       \<longrightarrow> \<not> result))"

theorem hasOppositeSign_spec_satisfied:
  assumes "hasOppositeSign_precond a b"
  shows "hasOppositeSign_postcond a b (hasOppositeSign a b)"
  sorry

end
