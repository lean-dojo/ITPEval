(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_to_divides, catalog title cong.congruent_to_divides:
  congruence modulo a positive natural modulus implies that the modulus
  divides the truncated natural-number difference. This file contains no
  proof.
*)

theory congruent_to_divides
  imports Main
begin

definition congruent :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "congruent n m p \<longleftrightarrow> n mod p = m mod p"

theorem congruent_to_divides:
  fixes n m p :: nat
  assumes "0 < p"
    and "congruent n m p"
  shows "p dvd (n - m)"
  sorry

end
