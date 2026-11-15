(*
  Statement-only formalization of the thousand-theorems corpus artifact Q26708
  (thousand-theorems__isabelle__Q26708), "Binomial theorem": in every
  commutative semiring, a natural power of a sum equals the finite sum of the
  corresponding binomial-coefficient terms. This file contains no proof.
*)

theory Q26708_binomial_theorem
  imports Main
begin

theorem add_pow:
  fixes x y :: "'a::comm_semiring_1"
    and n :: nat
  shows "(x + y) ^ n =
    (\<Sum>m<n + 1. x ^ m * y ^ (n - m) * of_nat (n choose m))"
  sorry

end
