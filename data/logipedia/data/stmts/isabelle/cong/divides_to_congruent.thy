(*
  Statement-only formalization of Logipedia corpus artifact
  cong.divides_to_congruent, catalog title cong.divides_to_congruent:
  divisibility of a truncated natural-number difference by a positive modulus
  implies congruence modulo that modulus. This file contains no proof.
*)

theory divides_to_congruent
  imports Main
begin

definition congruent :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "congruent n m p \<longleftrightarrow> n mod p = m mod p"

theorem divides_to_congruent:
  fixes n m p :: nat
  assumes "0 < p"
    and "m \<le> n"
    and "p dvd (n - m)"
  shows "congruent n m p"
  sorry

end
