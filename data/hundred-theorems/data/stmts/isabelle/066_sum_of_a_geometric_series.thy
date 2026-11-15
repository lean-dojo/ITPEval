(*
  Statement-only formalization of the sum of a geometric series from Hundred
  Theorems item 066. This file contains no proof.
*)

theory Sum_Of_A_Geometric_Series
  imports Complex_Main
begin

theorem geometric_series:
  fixes c :: "'a::real_normed_field"
  assumes "norm c < 1"
  shows "(\<lambda>n. c ^ n) sums (1 / (1 - c))"
  sorry

end
