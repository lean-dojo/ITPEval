(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a6
  (putnambench__isabelle__putnam_2025_a6): exact powers of two dividing a
  difference of terms in a recursively defined integer sequence. This file
  contains no proof.
*)

theory putnam_2025_a6
  imports Main
begin

primrec putnam_2025_a6_b :: "nat \<Rightarrow> int" where
  "putnam_2025_a6_b 0 = 0"
| "putnam_2025_a6_b (Suc n) =
    2 * putnam_2025_a6_b n ^ 2 + putnam_2025_a6_b n + 1"

theorem putnam_2025_a6:
  fixes k :: nat
  assumes "1 \<le> k"
  shows
    "(2 ^ (2 * k + 2) :: int)
        dvd (putnam_2025_a6_b (2 ^ (k + 1)) -
          2 * putnam_2025_a6_b (2 ^ k)) \<and>
      \<not> ((2 ^ (2 * k + 3) :: int)
        dvd (putnam_2025_a6_b (2 ^ (k + 1)) -
          2 * putnam_2025_a6_b (2 ^ k)))"
  sorry

end
