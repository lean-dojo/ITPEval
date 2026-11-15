(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q2226677 (thousand-theorems__isabelle__Q2226677), "Gelfand–Mazur theorem":
  the natural embedding of the complex numbers into a complete complex normed
  algebra in which precisely the nonzero elements are units is a complex
  algebra equivalence. This file contains no proof.
*)

theory Q2226677_gelfand_mazur_theorem
  imports Complex_Main
begin

definition q2226677_normed_ring ::
    "'a::{ring_1,real_normed_vector} itself \<Rightarrow> bool" where
  "q2226677_normed_ring _ \<longleftrightarrow>
    (\<forall>x y :: 'a. norm (x * y) \<le> norm x * norm y)"

definition q2226677_complex_normed_algebra ::
    "(complex \<Rightarrow> 'a::{ring_1,real_normed_vector} \<Rightarrow> 'a) \<Rightarrow> bool" where
  "q2226677_complex_normed_algebra scaleC \<longleftrightarrow>
    (\<forall>x. scaleC 0 x = 0) \<and>
    (\<forall>x. scaleC 1 x = x) \<and>
    (\<forall>z x y. scaleC z (x + y) = scaleC z x + scaleC z y) \<and>
    (\<forall>z w x. scaleC (z + w) x = scaleC z x + scaleC w x) \<and>
    (\<forall>z w x. scaleC (z * w) x = scaleC z (scaleC w x)) \<and>
    (\<forall>z x y. scaleC z (x * y) = scaleC z x * y) \<and>
    (\<forall>z x y. scaleC z (x * y) = x * scaleC z y) \<and>
    (\<forall>r x. scaleC (of_real r) x = scaleR r x) \<and>
    (\<forall>z x. norm (scaleC z x) \<le> norm z * norm x)"

definition q2226677_complex_alg_equiv ::
    "(complex \<Rightarrow> 'a::{ring_1,real_normed_vector} \<Rightarrow> 'a) \<Rightarrow>
      (complex \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> bool" where
  "q2226677_complex_alg_equiv scaleC f g \<longleftrightarrow>
    (\<forall>z. f z = scaleC z 1) \<and>
    f 0 = 0 \<and>
    f 1 = 1 \<and>
    (\<forall>z w. f (z + w) = f z + f w) \<and>
    (\<forall>z w. f (z * w) = f z * f w) \<and>
    (\<forall>c z. f (c * z) = scaleC c (f z)) \<and>
    (\<forall>z. g (f z) = z) \<and>
    (\<forall>x. f (g x) = x)"

theorem gelfand_mazur_theorem:
  fixes scaleC ::
    "complex \<Rightarrow> 'a::{ring_1,real_normed_vector,complete_space} \<Rightarrow> 'a"
  assumes normed_ring: "q2226677_normed_ring TYPE('a)"
    and complex_algebra: "q2226677_complex_normed_algebra scaleC"
    and division:
      "\<forall>a :: 'a. (\<exists>b. a * b = 1 \<and> b * a = 1) \<longleftrightarrow> a \<noteq> 0"
  shows "\<exists>f :: complex \<Rightarrow> 'a. \<exists>g :: 'a \<Rightarrow> complex.
    q2226677_complex_alg_equiv scaleC f g"
  sorry

end
