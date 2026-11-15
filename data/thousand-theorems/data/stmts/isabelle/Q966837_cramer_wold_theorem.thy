(*
  Statement-only formalization of the thousand-theorems corpus artifact Q966837
  (thousand-theorems__isabelle__Q966837), "Cramér–Wold theorem": random
  variables valued in an arbitrary finite-dimensional real inner-product space
  converge in distribution exactly when all of their real scalar projections
  converge in distribution. This file contains no proof.
*)

theory Q966837_cramer_wold_theorem
  imports Complex_Main
begin

definition q966837_sigma_algebra :: "'a set set \<Rightarrow> bool"
  where
    "q966837_sigma_algebra S \<longleftrightarrow>
      {} \<in> S \<and>
      UNIV \<in> S \<and>
      (\<forall>A \<in> S. - A \<in> S) \<and>
      (\<forall>A :: nat \<Rightarrow> 'a set.
        (\<forall>n. A n \<in> S) \<longrightarrow> (\<Union>n. A n) \<in> S)"

definition q966837_generated_sigma_algebra ::
    "'a set set \<Rightarrow> 'a set set"
  where
    "q966837_generated_sigma_algebra G =
      \<Inter>{S. q966837_sigma_algebra S \<and> G \<subseteq> S}"

definition q966837_borel_sets ::
    "'a::topological_space set set"
  where
    "q966837_borel_sets =
      q966837_generated_sigma_algebra {U. open U}"

definition q966837_probability_space ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q966837_probability_space S P \<longleftrightarrow>
      q966837_sigma_algebra S \<and>
      P {} = 0 \<and>
      P UNIV = 1 \<and>
      (\<forall>A \<in> S. 0 \<le> P A) \<and>
      (\<forall>A :: nat \<Rightarrow> 'a set.
        (\<forall>n. A n \<in> S) \<and>
        (\<forall>i j. i \<noteq> j \<longrightarrow> A i \<inter> A j = {})
        \<longrightarrow>
          summable (\<lambda>n. P (A n)) \<and>
          P (\<Union>n. A n) = (\<Sum>n. P (A n)))"

definition q966837_measurable ::
    "'a set set \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) \<Rightarrow> bool"
  where
    "q966837_measurable S f \<longleftrightarrow>
      (\<forall>B \<in> q966837_borel_sets. f -` B \<in> S)"

definition q966837_measurable_representative ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow>
      ('a \<Rightarrow> 'b::topological_space) \<Rightarrow>
      ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where
    "q966837_measurable_representative S P f g \<longleftrightarrow>
      q966837_measurable S g \<and>
      (\<exists>N \<in> S. P N = 0 \<and> (\<forall>x. x \<notin> N \<longrightarrow> f x = g x))"

definition q966837_tendsto_in_distribution ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow>
      (nat \<Rightarrow> 'a \<Rightarrow> 'b::topological_space) \<Rightarrow>
      'c set set \<Rightarrow> ('c set \<Rightarrow> real) \<Rightarrow>
      ('c \<Rightarrow> 'b) \<Rightarrow> bool"
  where
    "q966837_tendsto_in_distribution S P X S' P' X' \<longleftrightarrow>
      q966837_probability_space S P \<and>
      q966837_probability_space S' P' \<and>
      (\<exists>Y Y'.
        (\<forall>n. q966837_measurable_representative S P (X n) (Y n)) \<and>
        q966837_measurable_representative S' P' X' Y' \<and>
        (\<forall>C. closed C \<longrightarrow>
          (\<forall>epsilon > 0. \<exists>N. \<forall>n \<ge> N.
            P {omega. Y n omega \<in> C}
              \<le> P' {omega. Y' omega \<in> C} + epsilon)))"

definition q966837_real_inner_product_space ::
    "('a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q966837_real_inner_product_space inner_product \<longleftrightarrow>
      (\<forall>x y. inner_product x y = inner_product y x) \<and>
      (\<forall>x y z.
        inner_product (x + y) z =
          inner_product x z + inner_product y z) \<and>
      (\<forall>r x y.
        inner_product (r *\<^sub>R x) y = r * inner_product x y) \<and>
      (\<forall>x. inner_product x x = norm x ^ 2)"

definition q966837_finite_dimensional ::
    "('a::real_vector) itself \<Rightarrow> bool"
  where
    "q966837_finite_dimensional _ \<longleftrightarrow>
      (\<exists>B :: 'a set. finite B \<and> span B = UNIV)"

theorem cramer_wold_theorem:
  fixes S :: "'omega set set"
    and P :: "'omega set \<Rightarrow> real"
    and S' :: "'omega' set set"
    and P' :: "'omega' set \<Rightarrow> real"
    and X :: "nat \<Rightarrow> 'omega \<Rightarrow> 'e::real_normed_vector"
    and X' :: "'omega' \<Rightarrow> 'e"
    and inner_product :: "'e \<Rightarrow> 'e \<Rightarrow> real"
  assumes inner_product_space:
      "q966837_real_inner_product_space inner_product"
    and finite_dimensional:
      "q966837_finite_dimensional TYPE('e)"
    and P_probability: "q966837_probability_space S P"
    and P'_probability: "q966837_probability_space S' P'"
    and X'_ae_measurable:
      "\<exists>Y'. q966837_measurable_representative S' P' X' Y'"
    and X_ae_measurable:
      "\<And>n. \<exists>Y. q966837_measurable_representative S P (X n) Y"
  shows
    "q966837_tendsto_in_distribution S P X S' P' X' \<longleftrightarrow>
      (\<forall>t :: 'e.
        q966837_tendsto_in_distribution S P
          (\<lambda>n omega. inner_product (X n omega) t)
          S' P'
          (\<lambda>omega. inner_product (X' omega) t))"
  sorry

end
