(*
  Statement-only formalization of Leibniz's series for pi from Hundred
  Theorems item 026. This file contains no proof.
*)

theory Leibniz_Series_For_Pi
  imports Complex_Main
begin

theorem leibniz_series_for_pi:
  "(\<lambda>k::nat. (-1::real) ^ k / (2 * real k + 1)) sums (pi / 4)"
  sorry

end
