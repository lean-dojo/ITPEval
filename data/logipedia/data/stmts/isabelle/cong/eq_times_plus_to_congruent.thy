(*
  Statement-only formalization of Logipedia corpus artifact
  cong.eq_times_plus_to_congruent, catalog title
  cong.eq_times_plus_to_congruent: if a natural number is a natural multiple
  of a positive modulus plus another natural number, then the two numbers are
  congruent modulo that modulus. This file contains no proof.
*)

theory eq_times_plus_to_congruent
  imports Main
begin

definition congruent :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "congruent n m p \<longleftrightarrow> n mod p = m mod p"

theorem eq_times_plus_to_congruent:
  fixes n m p r :: nat
  assumes "0 < p"
    and "n = r * p + m"
  shows "congruent n m p"
  sorry

end
