(*
  Statement-only formalization of thousand-theorems corpus artifact Q1137206,
  "Taylor's theorem": the Lagrange and Cauchy forms of the remainder for a
  finite Taylor expansion of a real function on a closed interval. This file
  contains no proof.
*)

theory Q1137206_taylor_s_theorem
  imports "HOL-Analysis.Derivative"
begin

definition q1137206_real_deriv_within ::
    "(real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real" where
  "q1137206_real_deriv_within f S x =
    vector_derivative f (at x within S)"

fun q1137206_iterated_real_deriv_within ::
    "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real" where
  "q1137206_iterated_real_deriv_within 0 f S = f"
| "q1137206_iterated_real_deriv_within (Suc k) f S =
    (\<lambda>y. q1137206_real_deriv_within
      (q1137206_iterated_real_deriv_within k f S) S y)"

definition q1137206_cont_diff_on_up_to ::
    "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> bool" where
  "q1137206_cont_diff_on_up_to n f S \<longleftrightarrow>
    (\<forall>k \<le> n.
      continuous_on S (q1137206_iterated_real_deriv_within k f S) \<and>
      (k < n \<longrightarrow>
        q1137206_iterated_real_deriv_within k f S differentiable_on S))"

definition q1137206_taylor_within_eval ::
    "(real \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "q1137206_taylor_within_eval f n S x0 x =
    (\<Sum>k<Suc n.
      q1137206_iterated_real_deriv_within k f S x0 *
        (x - x0) ^ k / fact k)"

theorem taylor_mean_remainder_lagrange:
  fixes f :: "real \<Rightarrow> real"
    and x x0 :: real
    and n :: nat
  assumes "x0 < x"
    and "q1137206_cont_diff_on_up_to n f {x0..x}"
    and "q1137206_iterated_real_deriv_within n f {x0..x}
      differentiable_on {x0<..<x}"
  shows "\<exists>x' \<in> {x0<..<x}.
    f x - q1137206_taylor_within_eval f n {x0..x} x0 x =
      q1137206_iterated_real_deriv_within (Suc n) f {x0..x} x' *
        (x - x0) ^ (Suc n) / fact (Suc n)"
  sorry

theorem taylor_mean_remainder_cauchy:
  fixes f :: "real \<Rightarrow> real"
    and x x0 :: real
    and n :: nat
  assumes "x0 < x"
    and "q1137206_cont_diff_on_up_to n f {x0..x}"
    and "q1137206_iterated_real_deriv_within n f {x0..x}
      differentiable_on {x0<..<x}"
  shows "\<exists>x' \<in> {x0<..<x}.
    f x - q1137206_taylor_within_eval f n {x0..x} x0 x =
      q1137206_iterated_real_deriv_within (Suc n) f {x0..x} x' *
        (x - x') ^ n / fact n * (x - x0)"
  sorry

end
