(*
  Statement-only formalization of thousand-theorems corpus artifact Q810431
  (thousand-theorems__isabelle__Q810431), "Basel problem": the real series
  whose nth term is 1 divided by n squared sums to pi squared divided by 6.
  This file contains no proof.
*)

theory Q810431_basel_problem
  imports Complex_Main
begin

theorem hasSum_zeta_two:
  "(\<lambda>n::nat. (1::real) / (real n) ^ 2) sums (pi ^ 2 / 6)"
  sorry

end
