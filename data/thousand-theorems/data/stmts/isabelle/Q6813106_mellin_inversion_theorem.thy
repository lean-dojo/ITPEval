(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q6813106, "Mellin inversion theorem": at a positive real point of continuity,
  the inverse Mellin transform of a Mellin-convergent function equals the
  original function when its transform is integrable on the vertical line.
  This file contains no proof.
*)

theory Q6813106_mellin_inversion_theorem
  imports "HOL-Analysis.Bochner_Integration"
    "HOL-Analysis.Lebesgue_Measure"
    "HOL-Analysis.Complex_Transcendental"
begin

definition q6813106_complex_normed_vector ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q6813106_complex_normed_vector cscale \<longleftrightarrow>
    (\<forall>a x y. cscale a (x + y) = cscale a x + cscale a y) \<and>
    (\<forall>a b x. cscale (a + b) x = cscale a x + cscale b x) \<and>
    (\<forall>a b x. cscale (a * b) x = cscale a (cscale b x)) \<and>
    (\<forall>x. cscale 1 x = x) \<and>
    (\<forall>r x. cscale (of_real r) x = scaleR r x) \<and>
    (\<forall>a x. norm (cscale a x) = norm a * norm x)"

definition q6813106_ae_strongly_measurable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> bool" where
  "q6813106_ae_strongly_measurable M f \<longleftrightarrow>
    (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'e.
      (\<forall>n. simple_function M (s n)) \<and>
      (AE x in M. (\<lambda>n. s n x) \<longlonglongrightarrow> f x))"

definition q6813106_has_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> 'e \<Rightarrow> bool" where
  "q6813106_has_bochner_integral M f I \<longleftrightarrow>
    q6813106_ae_strongly_measurable M f \<and>
    (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'e.
      (\<forall>n. Bochner_Integration.simple_bochner_integrable M (s n)) \<and>
      ((\<lambda>n. \<integral>\<^sup>+x. ennreal (norm (f x - s n x)) \<partial>M)
        \<longlonglongrightarrow> 0) \<and>
      ((\<lambda>n. Bochner_Integration.simple_bochner_integral M (s n))
        \<longlonglongrightarrow> I))"

definition q6813106_integrable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> bool" where
  "q6813106_integrable M f \<longleftrightarrow>
    (\<exists>I. q6813106_has_bochner_integral M f I)"

definition q6813106_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> 'e" where
  "q6813106_bochner_integral M f =
    (if \<exists>I. q6813106_has_bochner_integral M f I
     then THE I. q6813106_has_bochner_integral M f I
     else 0)"

definition q6813106_mellin_convergent ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      (real \<Rightarrow> 'e) \<Rightarrow> complex \<Rightarrow> bool" where
  "q6813106_mellin_convergent cscale f s \<longleftrightarrow>
    q6813106_integrable (restrict_space lborel {0<..})
      (\<lambda>t. cscale ((of_real t :: complex) powr (s - 1)) (f t))"

definition q6813106_mellin ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      (real \<Rightarrow> 'e) \<Rightarrow> complex \<Rightarrow> 'e" where
  "q6813106_mellin cscale f s =
    q6813106_bochner_integral (restrict_space lborel {0<..})
      (\<lambda>t. cscale ((of_real t :: complex) powr (s - 1)) (f t))"

definition q6813106_vertical_integrable ::
    "(complex \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> real \<Rightarrow> bool" where
  "q6813106_vertical_integrable F r \<longleftrightarrow>
    q6813106_integrable lborel
      (\<lambda>y. F (of_real r + of_real y * \<i>))"

definition q6813106_mellin_inverse ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      real \<Rightarrow> (complex \<Rightarrow> 'e) \<Rightarrow> real \<Rightarrow> 'e" where
  "q6813106_mellin_inverse cscale r F x =
    scaleR (1 / (2 * pi))
      (q6813106_bochner_integral lborel
        (\<lambda>y.
          cscale
            ((of_real x :: complex) powr
              (- (of_real r + of_real y * \<i>)))
            (F (of_real r + of_real y * \<i>))))"

theorem mellin_inversion:
  fixes cscale ::
      "complex \<Rightarrow> 'e::{real_normed_vector,complete_space} \<Rightarrow> 'e"
    and sigma x :: real
    and f :: "real \<Rightarrow> 'e"
  assumes complex_space: "q6813106_complex_normed_vector cscale"
    and x_positive: "0 < x"
    and mellin_convergent:
      "q6813106_mellin_convergent cscale f (of_real sigma)"
    and transform_vertical_integrable:
      "q6813106_vertical_integrable (q6813106_mellin cscale f) sigma"
    and continuous_at_x: "continuous (at x) f"
  shows
    "q6813106_mellin_inverse cscale sigma
      (q6813106_mellin cscale f) x = f x"
  sorry

end
