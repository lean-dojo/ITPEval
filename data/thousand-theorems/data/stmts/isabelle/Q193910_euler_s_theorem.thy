(*
  Statement-only formalization of thousand-theorems corpus artifact Q193910
  (thousand-theorems__isabelle__Q193910), "Euler's theorem": for coprime
  natural numbers x and n, x raised to Euler's totient of n is congruent to
  one modulo n. This file contains no proof.
*)

theory Q193910_euler_s_theorem
  imports Main
begin

definition q193910_totient :: "nat \<Rightarrow> nat" where
  "q193910_totient n =
    card {k::nat. 0 < k \<and> k \<le> n \<and> coprime k n}"

theorem euler_s_theorem:
  fixes x n :: nat
  assumes "coprime x n"
  shows "(x ^ q193910_totient n) mod n = 1 mod n"
  sorry

end
