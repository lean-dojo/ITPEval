(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q338886 (thousand-theorems__isabelle__Q338886), "Divergence theorem":
  the Bochner integral of the divergence of a continuous vector field on an
  arbitrary finite-dimensional rectangular box equals the signed sum of its
  component integrals over the box faces, allowing a countable exceptional
  set for differentiability. This file contains no proof.
*)

theory Q338886_divergence_theorem
  imports
    "HOL-Analysis.Bochner_Integration"
    "HOL-Analysis.Derivative"
    "HOL-Analysis.Finite_Cartesian_Product"
    "HOL-Analysis.Finite_Product_Measure"
    "HOL-Analysis.Lebesgue_Measure"
begin

definition q338886_ae_strongly_measurable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool" where
  "q338886_ae_strongly_measurable M g \<longleftrightarrow>
    (\<exists>u :: nat \<Rightarrow> 'a \<Rightarrow> 'b.
      (\<forall>n. simple_function M (u n)) \<and>
      (AE x in M. (\<lambda>n. u n x) \<longlonglongrightarrow> g x))"

definition q338886_integrable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool" where
  "q338886_integrable M g \<longleftrightarrow>
    q338886_ae_strongly_measurable M g \<and>
    (\<integral>\<^sup>+ x. ennreal (norm (g x)) \<partial>M) < \<infinity>"

definition q338886_has_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> bool" where
  "q338886_has_bochner_integral M g I \<longleftrightarrow>
    q338886_ae_strongly_measurable M g \<and>
    (\<exists>u :: nat \<Rightarrow> 'a \<Rightarrow> 'b.
      (\<forall>n. Bochner_Integration.simple_bochner_integrable M (u n)) \<and>
      (\<lambda>n. \<integral>\<^sup>+ x. ennreal (norm (g x - u n x)) \<partial>M)
        \<longlonglongrightarrow> 0 \<and>
      (\<lambda>n. Bochner_Integration.simple_bochner_integral M (u n))
        \<longlonglongrightarrow> I)"

definition q338886_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b" where
  "q338886_bochner_integral M g =
    (if complete (UNIV :: 'b set) then
      if \<exists>I. q338886_has_bochner_integral M g I
      then THE I. q338886_has_bochner_integral M g I
      else 0
    else 0)"

definition q338886_integrable_on ::
    "'a measure \<Rightarrow> 'a set \<Rightarrow>
      ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool" where
  "q338886_integrable_on M A g \<longleftrightarrow>
    q338886_integrable (restrict_space M A) g"

definition q338886_bochner_integral_on ::
    "'a measure \<Rightarrow> 'a set \<Rightarrow>
      ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b" where
  "q338886_bochner_integral_on M A g =
    q338886_bochner_integral (restrict_space M A) g"

definition q338886_box ::
    "(real^'i::finite) \<Rightarrow> (real^'i) \<Rightarrow> (real^'i) set" where
  "q338886_box a b = {x. \<forall>i. a $ i \<le> x $ i \<and> x $ i \<le> b $ i}"

definition q338886_open_box ::
    "(real^'i::finite) \<Rightarrow> (real^'i) \<Rightarrow> (real^'i) set" where
  "q338886_open_box a b = {x. \<forall>i. a $ i < x $ i \<and> x $ i < b $ i}"

definition q338886_face_box ::
    "(real^'i::finite) \<Rightarrow> (real^'i) \<Rightarrow> 'i \<Rightarrow>
      ('i \<Rightarrow> real) set" where
  "q338886_face_box a b i =
    {y. \<forall>j \<in> UNIV - {i}. a $ j \<le> y j \<and> y j \<le> b $ j}"

definition q338886_face_measure ::
    "'i::finite \<Rightarrow> ('i \<Rightarrow> real) measure" where
  "q338886_face_measure i =
    PiM (UNIV - {i}) (\<lambda>_. (lborel :: real measure))"

definition q338886_insert_coordinate ::
    "'i::finite \<Rightarrow> real \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> (real^'i)" where
  "q338886_insert_coordinate i c y =
    (\<chi> j. if j = i then c else y j)"

definition q338886_divergence ::
    "((real^'i::finite) \<Rightarrow> (real^'i \<Rightarrow> ('e::real_normed_vector^'i))) \<Rightarrow>
      (real^'i) \<Rightarrow> 'e" where
  "q338886_divergence D x =
    (\<Sum>i\<in>UNIV. D x (axis i 1) $ i)"

theorem q338886_divergence_theorem:
  fixes a b :: "real^'i::finite"
    and f :: "(real^'i) \<Rightarrow> ('e::real_normed_vector^'i)"
    and D :: "(real^'i) \<Rightarrow> (real^'i \<Rightarrow> ('e^'i))"
    and s :: "(real^'i) set"
  assumes ordered_box: "\<And>i. a $ i \<le> b $ i"
    and linear_derivative_field: "\<And>x. bounded_linear (D x)"
    and exceptional_set: "countable s"
    and continuous_on_box: "continuous_on (q338886_box a b) f"
    and differentiable_off_countable:
      "\<And>x. x \<in> q338886_open_box a b - s \<Longrightarrow>
        (f has_derivative D x) (at x)"
    and integrable_divergence:
      "q338886_integrable_on lborel (q338886_box a b)
        (q338886_divergence D)"
  shows
    "q338886_bochner_integral_on lborel (q338886_box a b)
        (q338886_divergence D) =
      (\<Sum>i\<in>UNIV.
        q338886_bochner_integral_on
          (q338886_face_measure i)
          (q338886_face_box a b i)
          (\<lambda>y. f (q338886_insert_coordinate i (b $ i) y) $ i) -
        q338886_bochner_integral_on
          (q338886_face_measure i)
          (q338886_face_box a b i)
          (\<lambda>y. f (q338886_insert_coordinate i (a $ i) y) $ i))"
  sorry

end
