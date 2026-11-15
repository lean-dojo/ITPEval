(*
  Statement-only formalization of thousand-theorems corpus artifact Q1144897,
  "Brouwer fixed-point theorem": every continuous self-map of a nonempty
  compact convex subset of a finite-dimensional real normed vector space has
  a fixed point. This file contains no proof.
*)

theory Q1144897_brouwer_fixed_point_theorem
  imports "HOL-Analysis.Convex"
begin

definition q1144897_finite_dimensional ::
    "'a::real_vector itself \<Rightarrow> bool" where
  "q1144897_finite_dimensional _ \<longleftrightarrow>
    (\<exists>B :: 'a set. finite_dimensional_vector_space ((*\<^sub>R)) B)"

theorem brouwer_fixed_point:
  fixes S :: "'a::real_normed_vector set"
    and f :: "'a \<Rightarrow> 'a"
  assumes finite_dimensional:
      "q1144897_finite_dimensional TYPE('a)"
    and convex: "convex S"
    and compact: "compact S"
    and nonempty: "S \<noteq> {}"
    and continuous: "continuous_on S f"
    and self_map: "f \<in> S \<rightarrow> S"
  shows "\<exists>x \<in> S. f x = x"
  sorry

end
