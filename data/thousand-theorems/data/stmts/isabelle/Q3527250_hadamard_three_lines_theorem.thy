(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q3527250, "Hadamard three-lines theorem": a bounded complex-differentiable
  complex-normed-space-valued function on a vertical strip is bounded at each point by
  the geometric interpolation of its boundary-line norm suprema. This file
  contains no proof.
*)

theory Q3527250_hadamard_three_lines_theorem
  imports "HOL-Analysis.Complex_Transcendental"
begin

definition q3527250_complex_normed_vector ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q3527250_complex_normed_vector cscale \<longleftrightarrow>
    (\<forall>a x y. cscale a (x + y) = cscale a x + cscale a y) \<and>
    (\<forall>a b x. cscale (a + b) x = cscale a x + cscale b x) \<and>
    (\<forall>a b x. cscale (a * b) x = cscale a (cscale b x)) \<and>
    (\<forall>x. cscale 1 x = x) \<and>
    (\<forall>r x. cscale (of_real r) x = scaleR r x) \<and>
    (\<forall>a x. norm (cscale a x) = norm a * norm x)"

definition q3527250_has_complex_derivative ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      (complex \<Rightarrow> 'e) \<Rightarrow> 'e \<Rightarrow> complex \<Rightarrow> bool" where
  "q3527250_has_complex_derivative cscale f d z \<longleftrightarrow>
    ((\<lambda>w. cscale (inverse (w - z)) (f w - f z)) \<longlongrightarrow> d) (at z)"

definition q3527250_vertical_strip :: "real \<Rightarrow> real \<Rightarrow> complex set" where
  "q3527250_vertical_strip l u = {z. l < Re z \<and> Re z < u}"

definition q3527250_vertical_closed_strip ::
    "real \<Rightarrow> real \<Rightarrow> complex set" where
  "q3527250_vertical_closed_strip l u = {z. l \<le> Re z \<and> Re z \<le> u}"

definition q3527250_diff_cont_on_cl ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      (complex \<Rightarrow> 'e) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "q3527250_diff_cont_on_cl cscale f l u \<longleftrightarrow>
    (\<forall>z \<in> q3527250_vertical_strip l u.
      \<exists>d. q3527250_has_complex_derivative cscale f d z) \<and>
    continuous_on (q3527250_vertical_closed_strip l u) f"

definition q3527250_sSup_norm_im ::
    "(complex \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> real \<Rightarrow> real" where
  "q3527250_sSup_norm_im f x =
    Sup ((\<lambda>z. norm (f z)) ` {z. Re z = x})"

definition q3527250_interp_strip ::
    "(complex \<Rightarrow> 'e::real_normed_vector) \<Rightarrow>
      real \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> complex" where
  "q3527250_interp_strip f l u z =
    (if q3527250_sSup_norm_im f l = 0 \<or>
        q3527250_sSup_norm_im f u = 0
     then 0
     else
       (of_real (q3527250_sSup_norm_im f l) :: complex) powr
         (1 - ((z - of_real l) / (of_real u - of_real l))) *
       (of_real (q3527250_sSup_norm_im f u) :: complex) powr
         ((z - of_real l) / (of_real u - of_real l)))"

theorem q3527250_hadamard_three_lines:
  fixes cscale ::
      "complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e"
    and f :: "complex \<Rightarrow> 'e"
    and l u :: real
    and z :: complex
  assumes complex_space: "q3527250_complex_normed_vector cscale"
    and strip_nonempty: "l < u"
    and z_in_strip: "z \<in> q3527250_vertical_closed_strip l u"
    and diff_cont:
      "q3527250_diff_cont_on_cl cscale f l u"
    and bounded:
      "bdd_above
        ((\<lambda>w. norm (f w)) ` q3527250_vertical_closed_strip l u)"
  shows
    "norm (f z) \<le> norm (q3527250_interp_strip f l u z)"
  sorry

end
