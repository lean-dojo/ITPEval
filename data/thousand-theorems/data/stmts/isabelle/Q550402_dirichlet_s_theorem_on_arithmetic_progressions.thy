(*
  Statement-only formalization of thousand-theorems corpus artifact Q550402
  (thousand-theorems__isabelle__Q550402), "Dirichlet's theorem on arithmetic
  progressions": for a nonzero modulus and an invertible residue class, the
  set of natural primes in that residue class is infinite. This file contains
  no proof.
*)

theory Q550402_dirichlet_s_theorem_on_arithmetic_progressions
  imports Main
begin

definition q550402_prime :: "nat \<Rightarrow> bool" where
  "q550402_prime p \<longleftrightarrow>
    2 \<le> p \<and> (\<forall>d::nat. d dvd p \<longrightarrow> d = 1 \<or> d = p)"

theorem dirichlet_s_theorem_on_arithmetic_progressions:
  fixes q a :: nat
  assumes "q \<noteq> 0"
    and "coprime a q"
  shows "infinite {p::nat. q550402_prime p \<and> p mod q = a mod q}"
  sorry

end
