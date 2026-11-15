(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_times, catalog title cong.congruent_times: multiplication
  preserves congruence modulo a positive natural modulus. This file contains
  no proof.
*)

theory congruent_times
  imports Main
begin

definition congruent :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "congruent n m p \<longleftrightarrow> n mod p = m mod p"

theorem congruent_times:
  fixes n m n1 m1 p :: nat
  assumes "0 < p"
    and "congruent n n1 p"
    and "congruent m m1 p"
  shows "congruent (n * m) (n1 * m1) p"
  sorry

end
