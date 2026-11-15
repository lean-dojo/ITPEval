(*
  Statement-only formalization of thousand-theorems corpus artifact Q276082
  (thousand-theorems__isabelle__Q276082), "Wilson's theorem": for a prime
  natural number p, (p - 1)! is congruent to -1 modulo p. This file contains
  no proof.
*)

theory Q276082_wilson_s_theorem
  imports Main
begin

definition q276082_prime :: "nat \<Rightarrow> bool" where
  "q276082_prime p \<longleftrightarrow>
    2 \<le> p \<and> (\<forall>d::nat. d dvd p \<longrightarrow> d = 1 \<or> d = p)"

theorem wilsons_lemma:
  fixes p :: nat
  assumes "q276082_prime p"
  shows "int (fact (p - 1)) mod int p = (-1 :: int) mod int p"
  sorry

end
