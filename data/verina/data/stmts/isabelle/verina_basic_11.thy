(*
  Statement-only formalization of VERINA corpus artifact verina_basic_11,
  catalog title "lastDigit": an executable natural-number program returns the
  remainder modulo 10, together with its trivial precondition, last-digit
  postcondition, and correctness contract. This file contains no proof.
*)

theory verina_basic_11
  imports Main
begin

definition lastDigit_precond :: "nat \<Rightarrow> bool" where
  "lastDigit_precond n \<longleftrightarrow> True"

definition lastDigit :: "nat \<Rightarrow> nat" where
  "lastDigit n = n mod 10"

definition lastDigit_postcond :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "lastDigit_postcond n result \<longleftrightarrow>
    ((0 \<le> result \<and> result < 10) \<and>
     ((n mod 10) - result = 0 \<and> result - (n mod 10) = 0))"

theorem lastDigit_spec_satisfied:
  assumes "lastDigit_precond n"
  shows "lastDigit_postcond n (lastDigit n)"
  sorry

end
