(*
  Statement-only formalization of thousand-theorems corpus artifact Q1008566,
  "Gauss–Lucas theorem": every zero of the derivative of a nonconstant complex
  polynomial lies in the convex hull of its zeros, with the companion explicit
  derivative-root weighted center-of-mass identity. Polynomials use their
  finitely supported coefficient functions. This file contains no proof.
*)

theory Q1008566_gauss_lucas_theorem
  imports Complex_Main
begin

definition gauss_lucas_support :: "(nat \<Rightarrow> complex) \<Rightarrow> nat set" where
  "gauss_lucas_support p = {n. p n \<noteq> 0}"

definition gauss_lucas_positive_degree :: "(nat \<Rightarrow> complex) \<Rightarrow> bool" where
  "gauss_lucas_positive_degree p \<longleftrightarrow>
    finite (gauss_lucas_support p) \<and>
    (\<exists>n > 0. p n \<noteq> 0)"

definition gauss_lucas_poly_eval ::
    "(nat \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex" where
  "gauss_lucas_poly_eval p z =
    (\<Sum>n\<in>gauss_lucas_support p. p n * z ^ n)"

definition gauss_lucas_pderiv ::
    "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> complex" where
  "gauss_lucas_pderiv p n = of_nat (Suc n) * p (Suc n)"

definition gauss_lucas_root_multiplicity ::
    "(nat \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> nat" where
  "gauss_lucas_root_multiplicity p w =
    (LEAST n. gauss_lucas_poly_eval ((gauss_lucas_pderiv ^^ n) p) w \<noteq> 0)"

definition gauss_lucas_root_weight ::
    "(nat \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> real" where
  "gauss_lucas_root_weight p z w =
    (if gauss_lucas_poly_eval p z = 0 then
       if w = z then 1 else 0
     else real (gauss_lucas_root_multiplicity p w) / norm (z - w) ^ 2)"

definition gauss_lucas_center_mass ::
    "(nat \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex" where
  "gauss_lucas_center_mass p z =
    inverse
      (\<Sum>w | gauss_lucas_poly_eval p w = 0.
        gauss_lucas_root_weight p z w) *\<^sub>R
      (\<Sum>w | gauss_lucas_poly_eval p w = 0.
        gauss_lucas_root_weight p z w *\<^sub>R w)"

definition gauss_lucas_convex_hull :: "complex set \<Rightarrow> complex set" where
  "gauss_lucas_convex_hull s =
    {z. \<exists>u :: complex \<Rightarrow> real.
      finite {w. u w \<noteq> 0} \<and>
      {w. u w \<noteq> 0} \<subseteq> s \<and>
      (\<forall>w. 0 \<le> u w) \<and>
      (\<Sum>w | u w \<noteq> 0. u w) = 1 \<and>
      (\<Sum>w | u w \<noteq> 0. u w *\<^sub>R w) = z}"

theorem eq_center_mass_of_poly_pderiv_eq_zero:
  fixes p :: "nat \<Rightarrow> complex"
    and z :: complex
  assumes "gauss_lucas_positive_degree p"
    and "gauss_lucas_poly_eval (gauss_lucas_pderiv p) z = 0"
  shows "z = gauss_lucas_center_mass p z"
  sorry

theorem root_set_pderiv_subset_convex_hull_root_set:
  fixes p :: "nat \<Rightarrow> complex"
  assumes "gauss_lucas_positive_degree p"
  shows "{z. gauss_lucas_poly_eval (gauss_lucas_pderiv p) z = 0}
    \<subseteq> gauss_lucas_convex_hull {z. gauss_lucas_poly_eval p z = 0}"
  sorry

end
