(*
  Statement-only formalization of thousand-theorems corpus artifact Q7432915
  (thousand-theorems__isabelle__Q7432915), "Schroeder–Bernstein theorem for
  measurable spaces": measurable embeddings in both directions between two
  possibly empty measurable spaces yield a measurable equivalence. This file
  contains no proof.
*)

theory Q7432915_schroeder_bernstein_theorem_for_measurable_spaces
  imports Complex_Main
begin

definition q7432915_sigma_algebra ::
    "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "q7432915_sigma_algebra X S \<longleftrightarrow>
    S \<subseteq> Pow X \<and>
    {} \<in> S \<and>
    (\<forall>A \<in> S. X - A \<in> S) \<and>
    (\<forall>A :: nat \<Rightarrow> 'a set.
      (\<forall>n. A n \<in> S) \<longrightarrow> (\<Union>n. A n) \<in> S)"

definition q7432915_measurable ::
    "'a set \<Rightarrow> 'a set set \<Rightarrow>
      'b set \<Rightarrow> 'b set set \<Rightarrow>
      ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "q7432915_measurable X S Y T f \<longleftrightarrow>
    f ` X \<subseteq> Y \<and>
    (\<forall>B \<in> T. {x \<in> X. f x \<in> B} \<in> S)"

definition q7432915_measurable_embedding ::
    "'a set \<Rightarrow> 'a set set \<Rightarrow>
      'b set \<Rightarrow> 'b set set \<Rightarrow>
      ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "q7432915_measurable_embedding X S Y T f \<longleftrightarrow>
    inj_on f X \<and>
    q7432915_measurable X S Y T f \<and>
    (\<forall>A \<in> S. f ` A \<in> T)"

definition q7432915_measurable_equivalence ::
    "'a set \<Rightarrow> 'a set set \<Rightarrow>
      'b set \<Rightarrow> 'b set set \<Rightarrow>
      ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "q7432915_measurable_equivalence X S Y T h k \<longleftrightarrow>
    q7432915_measurable X S Y T h \<and>
    q7432915_measurable Y T X S k \<and>
    (\<forall>x \<in> X. k (h x) = x) \<and>
    (\<forall>y \<in> Y. h (k y) = y)"

theorem schroeder_bernstein_for_measurable_spaces:
  fixes X :: "'a set"
    and S :: "'a set set"
    and Y :: "'b set"
    and T :: "'b set set"
    and f :: "'a \<Rightarrow> 'b"
    and g :: "'b \<Rightarrow> 'a"
  assumes sigma_X: "q7432915_sigma_algebra X S"
    and sigma_Y: "q7432915_sigma_algebra Y T"
    and embedding_f: "q7432915_measurable_embedding X S Y T f"
    and embedding_g: "q7432915_measurable_embedding Y T X S g"
  shows "\<exists>h k.
    q7432915_measurable_equivalence X S Y T h k"
  sorry

end
