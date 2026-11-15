(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_n_n, catalog title cong.congruent_n_n: every natural number
  is congruent to itself modulo every natural modulus. This file contains no
  proof.
*)

theory congruent_n_n
  imports Main
begin

definition congruent :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "congruent n m p \<longleftrightarrow> n mod p = m mod p"

theorem congruent_n_n:
  fixes n p :: nat
  shows "congruent n n p"
  sorry

end
