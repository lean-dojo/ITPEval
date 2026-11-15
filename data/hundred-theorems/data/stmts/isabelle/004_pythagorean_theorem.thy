(*
  Statement-only formalization of the Pythagorean theorem from Hundred
  Theorems item 004. Orthogonal vectors have additive squared norms. This file
  contains no proof.
*)

theory Pythagorean_Theorem
  imports "HOL-Analysis.Inner_Product"
begin

theorem pythagorean_theorem:
  fixes x y :: "'a::real_inner"
  assumes "inner x y = 0"
  shows "norm (x + y) ^ 2 = norm x ^ 2 + norm y ^ 2"
  sorry

end
