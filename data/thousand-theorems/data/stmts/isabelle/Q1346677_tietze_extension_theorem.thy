(*
  Statement-only formalization of the thousand-theorems corpus artifact Q1346677,
  "Tietze extension theorem": a bounded continuous real-valued function along a
  closed embedding into a normal topological space has a bounded continuous
  extension with the same supremum norm. This file contains no proof.
*)

theory Q1346677_tietze_extension_theorem
  imports "HOL-Analysis.Abstract_Topology"
begin

definition q1346677_is_normal_space :: "'a topology \<Rightarrow> bool"
  where
    "q1346677_is_normal_space X \<longleftrightarrow>
      (\<forall>S T.
        closedin X S \<longrightarrow>
        closedin X T \<longrightarrow>
        disjnt S T \<longrightarrow>
        (\<exists>U V.
          openin X U \<and>
          openin X V \<and>
          S \<subseteq> U \<and>
          T \<subseteq> V \<and>
          disjnt U V))"

definition q1346677_is_closed_embedding ::
    "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where
    "q1346677_is_closed_embedding X Y e \<longleftrightarrow>
      embedding_map X Y e \<and> closedin Y (e ` topspace X)"

definition q1346677_is_bounded_continuous ::
    "'a topology \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q1346677_is_bounded_continuous X f \<longleftrightarrow>
      continuous_map X euclideanreal f \<and>
      (\<exists>B. \<forall>x\<in>topspace X. \<bar>f x\<bar> \<le> B)"

definition q1346677_bcf_norm ::
    "'a topology \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real"
  where
    "q1346677_bcf_norm X f =
      (if topspace X = {} then 0 else Sup ((\<lambda>x. \<bar>f x\<bar>) ` topspace X))"

theorem exists_extension_norm_eq_of_isClosedEmbedding:
  fixes X :: "'a topology"
    and Y :: "'b topology"
    and e :: "'a \<Rightarrow> 'b"
    and f :: "'a \<Rightarrow> real"
  assumes normal_Y: "q1346677_is_normal_space Y"
    and closed_embedding: "q1346677_is_closed_embedding X Y e"
    and bounded_continuous_f: "q1346677_is_bounded_continuous X f"
  shows "\<exists>g :: 'b \<Rightarrow> real.
    q1346677_is_bounded_continuous Y g \<and>
    q1346677_bcf_norm Y g = q1346677_bcf_norm X f \<and>
    (\<forall>x\<in>topspace X. g (e x) = f x)"
  sorry

end
