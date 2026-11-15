(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q727102, "Fermat's theorem (stationary points)": at a local minimum or
  maximum, the totalized real derivative and the totalized Frechet derivative
  of a real-valued function on an arbitrary real normed vector space are zero.
  This file contains no proof.
*)

theory Q727102_fermat_s_theorem_stationary_points
  imports "HOL-Analysis.Derivative"
begin

definition q727102_is_local_extr ::
    "('a::topological_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> bool" where
  "q727102_is_local_extr f a \<longleftrightarrow>
    eventually (\<lambda>x. f a \<le> f x) (nhds a) \<or>
    eventually (\<lambda>x. f x \<le> f a) (nhds a)"

definition q727102_fderiv ::
    "('a::real_normed_vector \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> real)" where
  "q727102_fderiv f a =
    (if \<exists>D. (f has_derivative D) (at a)
     then (SOME D. (f has_derivative D) (at a))
     else (\<lambda>_. 0))"

definition q727102_deriv ::
    "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "q727102_deriv f a =
    (if \<exists>d. DERIV f a :> d then (SOME d. DERIV f a :> d) else 0)"

theorem IsLocalExtr_fderiv_eq_zero:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
    and a :: 'a
  assumes "q727102_is_local_extr f a"
  shows "q727102_fderiv f a = (\<lambda>_. 0)"
  sorry

theorem IsLocalExtr_deriv_eq_zero:
  fixes f :: "real \<Rightarrow> real"
    and a :: real
  assumes "q727102_is_local_extr f a"
  shows "q727102_deriv f a = 0"
  sorry

end
