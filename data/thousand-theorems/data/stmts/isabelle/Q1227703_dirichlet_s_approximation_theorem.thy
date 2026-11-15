(*
  Statement-only formalization of thousand-theorems corpus artifact Q1227703,
  "Dirichlet's approximation theorem": every point on an additive circle of
  positive circumference has a nonzero multiple, bounded by a given positive
  integer, whose distance to zero is at most the circumference divided by the
  successor of that integer. This file contains no proof.
*)

theory Q1227703_dirichlet_s_approximation_theorem
  imports Complex_Main
begin

theorem dirichlet_s_approximation_theorem:
  fixes T x :: real
    and n :: nat
  assumes "0 < T"
    and "0 < n"
  shows "\<exists>j::nat. 1 \<le> j \<and> j \<le> n \<and>
    (\<exists>k::int.
      abs (real j * x - of_int k * T) \<le> T / real (n + 1))"
  sorry

end
