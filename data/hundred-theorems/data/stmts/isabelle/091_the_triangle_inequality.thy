(*
  Statement-only formalization of the triangle inequality from Hundred
  Theorems item 091. This file contains no proof.
*)

theory Triangle_Inequality
  imports "HOL-Analysis.Inner_Product"
begin

theorem triangle_inequality:
  fixes x y :: "'a::real_normed_vector"
  shows "norm (x + y) \<le> norm x + norm y"
  sorry

end
