(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_n_mod_n, catalog title cong.congruent_n_mod_n: for every
  natural number n and positive natural modulus p, n is congruent to its
  remainder modulo p. This file contains no proof.
*)

theory congruent_n_mod_n
  imports Main
begin

definition congruent :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "congruent n m p \<longleftrightarrow> n mod p = m mod p"

theorem congruent_n_mod_n:
  fixes n p :: nat
  assumes "0 < p"
  shows "congruent n (n mod p) p"
  sorry

end
