(*
  Statement-only formalization of "Dirichlet's Theorem" from Hundred Theorems item 048.
  For every positive natural modulus and coprime residue, infinitely many natural primes are
  congruent to that residue modulo the modulus. This file contains no proof.
*)

theory Dirichlets_Theorem
  imports Complex_Main
begin

definition nat_prime :: "nat \<Rightarrow> bool" where
  "nat_prime p \<longleftrightarrow>
    1 < p \<and> (\<forall>m :: nat. m dvd p \<longrightarrow> m = 1 \<or> m = p)"

theorem dirichlets_theorem:
  fixes d k :: nat
  assumes "1 \<le> d"
    and "coprime k d"
  shows "infinite {p :: nat. nat_prime p \<and> p mod d = k mod d}"
  sorry

end
