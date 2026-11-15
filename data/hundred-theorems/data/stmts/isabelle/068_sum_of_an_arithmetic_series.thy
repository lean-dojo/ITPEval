(*
  Statement-only formalization of "Sum of an Arithmetic Series" from Hundred Theorems item 068.
  It states the closed formula for the sum of the first n + 1 terms of a natural-number
  arithmetic progression.
  This file contains no proof.
*)

theory Sum_of_an_Arithmetic_Series
  imports Main
begin

theorem arithmetic_series_sum:
  fixes a d n :: nat
  shows "2 * (\<Sum>i = 0..n. a + i * d) =
    Suc n * (2 * a + n * d)"
  sorry

end
