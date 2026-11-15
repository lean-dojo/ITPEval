(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q576478, "Liouville's theorem (complex analysis)": an everywhere complex
  Frechet-differentiable map between arbitrary complex normed vector spaces
  with bounded range takes equal values at every two points. This file contains
  no proof.
*)

theory Q576478_liouville_s_theorem_complex_analysis
  imports "HOL-Analysis.Complex_Analysis_Basics"
begin

definition q576478_complex_normed_vector ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q576478_complex_normed_vector cscale \<longleftrightarrow>
    (\<forall>a x y. cscale a (x + y) = cscale a x + cscale a y) \<and>
    (\<forall>a b x. cscale (a + b) x = cscale a x + cscale b x) \<and>
    (\<forall>a b x. cscale (a * b) x = cscale a (cscale b x)) \<and>
    (\<forall>x. cscale 1 x = x) \<and>
    (\<forall>r x. cscale (of_real r) x = scaleR r x) \<and>
    (\<forall>a x. norm (cscale a x) = norm a * norm x)"

definition q576478_complex_differentiable ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      (complex \<Rightarrow> 'f::real_normed_vector \<Rightarrow> 'f) \<Rightarrow>
      ('e \<Rightarrow> 'f) \<Rightarrow> bool" where
  "q576478_complex_differentiable cscaleE cscaleF f \<longleftrightarrow>
    (\<forall>x. \<exists>D.
      (f has_derivative D) (at x) \<and>
      (\<forall>a v. D (cscaleE a v) = cscaleF a (D v)))"

theorem q576478_liouville:
  fixes cscaleE :: "complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e"
    and cscaleF :: "complex \<Rightarrow> 'f::real_normed_vector \<Rightarrow> 'f"
    and f :: "'e \<Rightarrow> 'f"
    and z w :: 'e
  assumes domain_complex_space: "q576478_complex_normed_vector cscaleE"
    and codomain_complex_space: "q576478_complex_normed_vector cscaleF"
    and differentiable:
      "q576478_complex_differentiable cscaleE cscaleF f"
    and bounded_range: "bounded (range f)"
  shows "f z = f w"
  sorry

end
