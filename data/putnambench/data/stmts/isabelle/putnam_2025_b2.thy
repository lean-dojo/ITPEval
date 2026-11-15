(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b2
  (putnambench__isabelle__putnam_2025_b2): for a continuous, strictly
  increasing, nonnegative real function on [0,1], the x-coordinate of the
  centroid weighted by the square of the function exceeds the one weighted
  by the function. This file contains no proof.
*)

theory putnam_2025_b2
  imports Complex_Main
begin

definition putnam_2025_b2_integral :: "(real \<Rightarrow> real) \<Rightarrow> real" where
  "putnam_2025_b2_integral g =
    Lim sequentially
      (\<lambda>n :: nat.
        if n = 0 then 0
        else (\<Sum>k<n. g (real k / real n)) / real n)"

theorem putnam_2025_b2:
  fixes f :: "real \<Rightarrow> real"
  assumes hf_cont: "continuous_on {0..1} f"
    and hf_mono: "strict_mono_on {0..1} f"
    and hf_nonneg: "\<forall>x \<in> {0..1}. 0 \<le> f x"
  shows
    "putnam_2025_b2_integral (\<lambda>x. x * f x) /
        putnam_2025_b2_integral f
      <
      putnam_2025_b2_integral (\<lambda>x. x * (f x) ^ 2) /
        putnam_2025_b2_integral (\<lambda>x. (f x) ^ 2)"
  sorry

end
