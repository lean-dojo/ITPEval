(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b5
  (putnambench__isabelle__putnam_2025_b5): a lower bound for the number of
  descents among consecutive canonical multiplicative inverses modulo a prime.
  This file contains no proof.
*)

theory putnam_2025_b5
  imports "HOL-Computational_Algebra.Primes"
begin

definition putnam_2025_b5_mod_inv :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "putnam_2025_b5_mod_inv p k =
    (THE x. x \<in> {1..<p} \<and> (k * x) mod p = 1)"

definition putnam_2025_b5_descent_count :: "nat \<Rightarrow> nat" where
  "putnam_2025_b5_descent_count p =
    card {k \<in> {1..p - 2}.
      putnam_2025_b5_mod_inv p (k + 1) < putnam_2025_b5_mod_inv p k}"

theorem putnam_2025_b5:
  fixes p :: nat
  assumes hp_prime: "prime p"
    and hp_gt: "3 < p"
  shows
    "rat_of_nat p / 4 - 1 <
      rat_of_nat (putnam_2025_b5_descent_count p)"
  sorry

end
