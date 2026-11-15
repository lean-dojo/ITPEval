(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1140119 (thousand-theorems__isabelle__Q1140119), "Morera's theorem":
  for a function from the complex plane to a complete complex normed vector
  space on an open set, vanishing oriented integrals around every
  axis-parallel rectangle together with continuity is equivalent to complex
  differentiability on that set. This file contains no proof.
*)

theory Q1140119_morera_s_theorem
  imports Complex_Main
begin

definition q1140119_complex_normed_vector ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1140119_complex_normed_vector cscale \<longleftrightarrow>
    (\<forall>a x y. cscale a (x + y) = cscale a x + cscale a y) \<and>
    (\<forall>a b x. cscale (a + b) x = cscale a x + cscale b x) \<and>
    (\<forall>a b x. cscale (a * b) x = cscale a (cscale b x)) \<and>
    (\<forall>x. cscale 1 x = x) \<and>
    (\<forall>r x. cscale (of_real r) x = scaleR r x) \<and>
    (\<forall>a x. norm (cscale a x) = norm a * norm x)"

definition q1140119_riemann_sum ::
    "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
      (real \<Rightarrow> 'e::real_normed_vector) \<Rightarrow> 'e" where
  "q1140119_riemann_sum n a b g =
    (if n = 0 then 0 else
      (\<Sum>k<n.
        ((b - a) / real n) *\<^sub>R
          g (a + (real k / real n) * (b - a))))"

definition q1140119_directed_integral ::
    "real \<Rightarrow> real \<Rightarrow>
      (real \<Rightarrow> 'e::{real_normed_vector,complete_space}) \<Rightarrow> 'e" where
  "q1140119_directed_integral a b g =
    Lim at_top (\<lambda>n. q1140119_riemann_sum n a b g)"

definition q1140119_rectangle :: "complex \<Rightarrow> complex \<Rightarrow> complex set" where
  "q1140119_rectangle z w =
    {u. min (Re z) (Re w) \<le> Re u \<and> Re u \<le> max (Re z) (Re w) \<and>
        min (Im z) (Im w) \<le> Im u \<and> Im u \<le> max (Im z) (Im w)}"

definition q1140119_wedge_integral ::
    "(complex \<Rightarrow> 'e::{real_normed_vector,complete_space} \<Rightarrow> 'e) \<Rightarrow>
      complex \<Rightarrow> complex \<Rightarrow> (complex \<Rightarrow> 'e) \<Rightarrow> 'e" where
  "q1140119_wedge_integral cscale z w f =
    q1140119_directed_integral (Re z) (Re w)
      (\<lambda>x. f (of_real x + of_real (Im z) * \<i>)) +
    cscale \<i>
      (q1140119_directed_integral (Im z) (Im w)
        (\<lambda>y. f (of_real (Re w) + of_real y * \<i>)))"

definition q1140119_is_conservative_on ::
    "(complex \<Rightarrow> 'e::{real_normed_vector,complete_space} \<Rightarrow> 'e) \<Rightarrow>
      (complex \<Rightarrow> 'e) \<Rightarrow> complex set \<Rightarrow> bool" where
  "q1140119_is_conservative_on cscale f U \<longleftrightarrow>
    (\<forall>z w. q1140119_rectangle z w \<subseteq> U \<longrightarrow>
      q1140119_wedge_integral cscale z w f =
        - q1140119_wedge_integral cscale w z f)"

definition q1140119_complex_differentiable_on ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      (complex \<Rightarrow> 'e) \<Rightarrow> complex set \<Rightarrow> bool" where
  "q1140119_complex_differentiable_on cscale f U \<longleftrightarrow>
    (\<forall>z \<in> U. \<exists>d.
      ((\<lambda>w. cscale (inverse (w - z)) (f w - f z)) \<longlongrightarrow> d)
        (at z within (U - {z})))"

theorem q1140119_morera_s_theorem:
  fixes cscale ::
      "complex \<Rightarrow> 'e::{real_normed_vector,complete_space} \<Rightarrow> 'e"
    and f :: "complex \<Rightarrow> 'e"
    and U :: "complex set"
  assumes complex_space: "q1140119_complex_normed_vector cscale"
    and open_set: "open U"
  shows
    "q1140119_is_conservative_on cscale f U \<and> continuous_on U f
      \<longleftrightarrow> q1140119_complex_differentiable_on cscale f U"
  sorry

end
