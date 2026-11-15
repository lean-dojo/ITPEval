(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q2096184, "Plancherel theorem": the Fourier transform preserves the
  integrated complex inner product of arbitrary Hilbert-space-valued Schwartz
  functions on a finite-dimensional real inner product space. This file
  contains no proof.
*)

theory Q2096184_plancherel_theorem
  imports "HOL-Analysis.Bochner_Integration" "HOL-Analysis.Lebesgue_Measure"
begin

definition q2096184_complex_hilbert_space ::
    "(complex \<Rightarrow> 'h::real_normed_vector \<Rightarrow> 'h) \<Rightarrow>
      ('h \<Rightarrow> 'h \<Rightarrow> complex) \<Rightarrow> bool" where
  "q2096184_complex_hilbert_space cscale cinner \<longleftrightarrow>
    (\<forall>a x y. cscale a (x + y) = cscale a x + cscale a y) \<and>
    (\<forall>a b x. cscale (a + b) x = cscale a x + cscale b x) \<and>
    (\<forall>a b x. cscale (a * b) x = cscale a (cscale b x)) \<and>
    (\<forall>x. cscale 1 x = x) \<and>
    (\<forall>r x. cscale (of_real r) x = scaleR r x) \<and>
    (\<forall>a x. norm (cscale a x) = norm a * norm x) \<and>
    (\<forall>x y z. cinner (x + y) z = cinner x z + cinner y z) \<and>
    (\<forall>a x y. cinner (cscale a x) y = cnj a * cinner x y) \<and>
    (\<forall>x y z. cinner x (y + z) = cinner x y + cinner x z) \<and>
    (\<forall>a x y. cinner x (cscale a y) = a * cinner x y) \<and>
    (\<forall>x y. cinner x y = cnj (cinner y x)) \<and>
    (\<forall>x. cinner x x = of_real (norm x ^ 2))"

definition q2096184_orthonormal_basis ::
    "'v::real_inner set \<Rightarrow> bool" where
  "q2096184_orthonormal_basis B \<longleftrightarrow>
    finite_dimensional_vector_space
      ((*\<^sub>R) :: real \<Rightarrow> 'v \<Rightarrow> 'v) B \<and>
    (\<forall>u \<in> B. \<forall>v \<in> B. inner u v = (if u = v then 1 else 0))"

definition q2096184_parallelotope ::
    "'v::real_vector set \<Rightarrow> 'v set" where
  "q2096184_parallelotope B =
    {(\<Sum>b\<in>B. c b *\<^sub>R b) | c. \<forall>b \<in> B. 0 \<le> c b \<and> c b < 1}"

definition q2096184_lebesgue_measure ::
    "'v::real_inner measure \<Rightarrow> bool" where
  "q2096184_lebesgue_measure M \<longleftrightarrow>
    sets M = sets borel \<and>
    (\<forall>a. distr M borel ((+) a) = M) \<and>
    (\<forall>B. q2096184_orthonormal_basis B \<longrightarrow>
      measure M (q2096184_parallelotope B) = 1)"

fun q2096184_iterated_directional_derivative ::
    "('v::real_normed_vector \<Rightarrow> 'h::real_normed_vector) \<Rightarrow>
      'v list \<Rightarrow> 'v \<Rightarrow> 'h" where
  "q2096184_iterated_directional_derivative f [] x = f x"
| "q2096184_iterated_directional_derivative f (v # vs) x =
    frechet_derivative
      (q2096184_iterated_directional_derivative f vs) (at x) v"

definition q2096184_schwartz ::
    "('v::real_normed_vector \<Rightarrow> 'h::real_normed_vector) \<Rightarrow> bool" where
  "q2096184_schwartz f \<longleftrightarrow>
    (\<forall>vs x.
      q2096184_iterated_directional_derivative f vs differentiable (at x)) \<and>
    (\<forall>vs n. \<exists>C::real. 0 \<le> C \<and>
      (\<forall>x. (1 + norm x) ^ n *
        norm (q2096184_iterated_directional_derivative f vs x) \<le> C))"

definition q2096184_ae_strongly_measurable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool" where
  "q2096184_ae_strongly_measurable M f \<longleftrightarrow>
    (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'b.
      (\<forall>n. simple_function M (s n)) \<and>
      (AE x in M. (\<lambda>n. s n x) \<longlonglongrightarrow> f x))"

definition q2096184_has_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> bool" where
  "q2096184_has_bochner_integral M f I \<longleftrightarrow>
    q2096184_ae_strongly_measurable M f \<and>
    (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'b.
      (\<forall>n. Bochner_Integration.simple_bochner_integrable M (s n)) \<and>
      ((\<lambda>n. \<integral>\<^sup>+x. ennreal (norm (f x - s n x)) \<partial>M)
        \<longlonglongrightarrow> 0) \<and>
      ((\<lambda>n. Bochner_Integration.simple_bochner_integral M (s n))
        \<longlonglongrightarrow> I))"

definition q2096184_bochner_integral ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b" where
  "q2096184_bochner_integral M f =
    (if \<exists>I. q2096184_has_bochner_integral M f I
     then THE I. q2096184_has_bochner_integral M f I
     else 0)"

definition q2096184_fourier ::
    "(complex \<Rightarrow> 'h::real_normed_vector \<Rightarrow> 'h) \<Rightarrow>
      'v::{real_inner,real_normed_vector} measure \<Rightarrow>
      ('v \<Rightarrow> 'h) \<Rightarrow> 'v \<Rightarrow> 'h" where
  "q2096184_fourier cscale M f xi =
    q2096184_bochner_integral M
      (\<lambda>x. cscale
        (exp (- (\<i> * of_real (2 * pi * inner x xi)))) (f x))"

theorem integral_inner_fourier_fourier:
  fixes M :: "'v::{real_inner,real_normed_vector} measure"
    and cscale ::
      "complex \<Rightarrow> 'h::{real_normed_vector,complete_space} \<Rightarrow> 'h"
    and cinner :: "'h \<Rightarrow> 'h \<Rightarrow> complex"
    and f g :: "'v \<Rightarrow> 'h"
  assumes finite_dimensional: "\<exists>B. q2096184_orthonormal_basis B"
    and lebesgue_measure: "q2096184_lebesgue_measure M"
    and hilbert_space: "q2096184_complex_hilbert_space cscale cinner"
    and f_schwartz: "q2096184_schwartz f"
    and g_schwartz: "q2096184_schwartz g"
  shows
    "q2096184_bochner_integral M
        (\<lambda>xi. cinner (q2096184_fourier cscale M f xi)
          (q2096184_fourier cscale M g xi)) =
      q2096184_bochner_integral M
        (\<lambda>x. cinner (f x) (g x))"
  sorry

end
