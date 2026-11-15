(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q834025, "Cauchy integral theorem": the Cauchy integral formula for a
  complex-valued function continuous on a closed disc and complex
  differentiable in its interior outside a countable exceptional set. The
  positively oriented circle integral is represented by its standard
  parametrized Riemann sums. This file contains no proof.
*)

theory Q834025_cauchy_integral_theorem
  imports Complex_Main
begin

definition q834025_complex_differentiable_at ::
    "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> bool"
  where
    "q834025_complex_differentiable_at f z \<longleftrightarrow>
      (\<exists>d. ((\<lambda>h. (f (z + h) - f z) / h) \<longlongrightarrow> d) (at 0))"

definition q834025_circle_point ::
    "complex \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex"
  where
    "q834025_circle_point c R t =
      c + of_real R * exp (2 * of_real pi * \<i> * of_real t)"

definition q834025_circle_velocity ::
    "real \<Rightarrow> real \<Rightarrow> complex"
  where
    "q834025_circle_velocity R t =
      of_real R * (2 * of_real pi * \<i>) *
        exp (2 * of_real pi * \<i> * of_real t)"

definition q834025_circle_riemann_sum ::
    "nat \<Rightarrow> complex \<Rightarrow> real \<Rightarrow>
      (complex \<Rightarrow> complex) \<Rightarrow> complex"
  where
    "q834025_circle_riemann_sum n c R g =
      (if n = 0 then 0 else
        (\<Sum>k<n.
          g (q834025_circle_point c R (real k / real n)) *
          q834025_circle_velocity R (real k / real n) *
          of_real (1 / real n)))"

definition q834025_circle_integral ::
    "complex \<Rightarrow> real \<Rightarrow>
      (complex \<Rightarrow> complex) \<Rightarrow> complex"
  where
    "q834025_circle_integral c R g =
      Lim at_top (\<lambda>n. q834025_circle_riemann_sum n c R g)"

theorem q834025_cauchy_integral_formula_off_countable:
  fixes R :: real
    and c w :: complex
    and s :: "complex set"
    and f :: "complex \<Rightarrow> complex"
  assumes exceptional_set: "countable s"
    and interior_point: "w \<in> ball c R"
    and continuous_closed_disc: "continuous_on (cball c R) f"
    and differentiable_off_countable:
      "\<And>z. z \<in> ball c R - s \<Longrightarrow>
        q834025_complex_differentiable_at f z"
  shows
    "q834025_circle_integral c R (\<lambda>z. f z / (z - w)) =
      2 * of_real pi * \<i> * f w"
  oops

end
