(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a1
  (putnambench__isabelle__putnam_2024_a1): the positive natural exponents
  admitting positive natural numbers a, b, and c with
  2*a^n + 3*b^n = 4*c^n are exactly n = 1. This file contains no proof.
*)

theory putnam_2024_a1
  imports Complex_Main
begin

definition putnam_2024_a1_solution :: "nat set" where
  "putnam_2024_a1_solution = {1}"

theorem putnam_2024_a1:
  shows
    "{n :: nat.
      0 < n \<and>
      (\<exists>a b c :: nat.
        0 < a \<and>
        0 < b \<and>
        0 < c \<and>
        2 * a ^ n + 3 * b ^ n = 4 * c ^ n)}
      = putnam_2024_a1_solution"
  sorry

end
