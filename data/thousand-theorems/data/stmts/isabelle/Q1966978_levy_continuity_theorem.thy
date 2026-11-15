(*
  Statement-only formalization of the thousand-theorems corpus artifact Q1966978
  (thousand-theorems__isabelle__Q1966978), "Lévy continuity theorem": for Borel
  probability measures on an arbitrary finite-dimensional real inner-product
  space, weak convergence is equivalent to pointwise convergence of their
  characteristic functions. This file contains no proof.
*)

theory Q1966978_levy_continuity_theorem
  imports "HOL-Probability.Levy"
begin

definition q1966978_probability_measure ::
    "'a::euclidean_space measure \<Rightarrow> bool"
  where
    "q1966978_probability_measure M \<longleftrightarrow>
      sets M = sets borel \<and> emeasure M UNIV = 1"

definition q1966978_weak_convergence ::
    "(nat \<Rightarrow> 'a::euclidean_space measure) \<Rightarrow> 'a measure \<Rightarrow> bool"
  where
    "q1966978_weak_convergence M M0 \<longleftrightarrow>
      (\<forall>f :: 'a \<Rightarrow> real.
        bounded (range f) \<and> continuous_on UNIV f \<longrightarrow>
        (\<lambda>n. integral\<^sup>L (M n) f)
          \<longlonglongrightarrow> integral\<^sup>L M0 f)"

definition q1966978_characteristic_function ::
    "'a::euclidean_space measure \<Rightarrow> 'a \<Rightarrow> complex"
  where
    "q1966978_characteristic_function M t =
      integral\<^sup>L M (\<lambda>x. iexp (inner t x))"

theorem levy_continuity_theorem:
  fixes M :: "nat \<Rightarrow> 'a::euclidean_space measure"
    and M0 :: "'a measure"
  assumes M_probability: "\<And>n. q1966978_probability_measure (M n)"
    and M0_probability: "q1966978_probability_measure M0"
  shows
    "q1966978_weak_convergence M M0 \<longleftrightarrow>
      (\<forall>t :: 'a.
        (\<lambda>n. q1966978_characteristic_function (M n) t)
          \<longlonglongrightarrow> q1966978_characteristic_function M0 t)"
  sorry

end
