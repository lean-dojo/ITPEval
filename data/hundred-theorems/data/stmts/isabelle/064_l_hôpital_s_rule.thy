(*
  Statement-only formalization of L'Hopital's rule from Hundred Theorems
  item 064. This is Isabelle/HOL's punctured-neighborhood zero-over-zero
  formulation. This file contains no proof.
*)

theory LHopitals_Rule
  imports Complex_Main
begin

theorem hundred_theorems_lhopital:
  fixes f g f' g' :: "real \<Rightarrow> real"
    and x :: real
  assumes f_zero: "(f \<longlongrightarrow> 0) (at x)"
    and g_zero: "(g \<longlongrightarrow> 0) (at x)"
    and g'_nonzero: "eventually (\<lambda>y. g' y \<noteq> 0) (at x)"
    and f_deriv: "eventually (\<lambda>y. DERIV f y :> f' y) (at x)"
    and g_deriv: "eventually (\<lambda>y. DERIV g y :> g' y) (at x)"
    and derivative_ratio:
      "filterlim (\<lambda>y. f' y / g' y) F (at x)"
  shows "filterlim (\<lambda>y. f y / g y) F (at x)"
  sorry

end
