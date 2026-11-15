(*
  Statement-only formalization of the thousand-theorems corpus artifact Q189136,
  "Mean value theorem": Lagrange's and Cauchy's mean value theorems for
  real-valued functions on a closed interval. This file contains no proof.
*)

theory Q189136_mean_value_theorem
  imports "HOL-Analysis.Derivative"
begin

theorem exists_deriv_eq_slope:
  fixes f :: "real \<Rightarrow> real"
    and a b :: real
  assumes "a < b"
    and "continuous_on {a..b} f"
    and "f differentiable_on {a<..<b}"
  shows "\<exists>c \<in> {a<..<b}.
    deriv f c = (f b - f a) / (b - a)"
  sorry

theorem exists_ratio_deriv_eq_ratio_slope:
  fixes f g :: "real \<Rightarrow> real"
    and a b :: real
  assumes "a < b"
    and "continuous_on {a..b} f"
    and "f differentiable_on {a<..<b}"
    and "continuous_on {a..b} g"
    and "g differentiable_on {a<..<b}"
  shows "\<exists>c \<in> {a<..<b}.
    (g b - g a) * deriv f c = (f b - f a) * deriv g c"
  sorry

end
