(*
  Statement-only formalization of the thousand-theorems corpus artifact Q2631152,
  "Carathéodory's extension theorem": the measure constructed from a
  sigma-subadditive additive content on a generating semiring agrees with that
  content on every set in the semiring. This file contains no proof.
*)

theory Q2631152_caratheodory_s_extension_theorem
  imports "HOL-Analysis.Caratheodory"
begin

definition q2631152_set_semiring :: "'a set set \<Rightarrow> bool" where
  "q2631152_set_semiring C \<longleftrightarrow>
    {} \<in> C \<and>
    (\<forall>s \<in> C. \<forall>t \<in> C. s \<inter> t \<in> C) \<and>
    (\<forall>s \<in> C. \<forall>t \<in> C.
      \<exists>I. finite I \<and> I \<subseteq> C \<and> disjoint I \<and>
        s - t = \<Union>I)"

definition q2631152_add_content ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> ennreal) \<Rightarrow> bool" where
  "q2631152_add_content C m \<longleftrightarrow>
    m {} = 0 \<and>
    (\<forall>I. finite I \<longrightarrow> I \<subseteq> C \<longrightarrow> disjoint I \<longrightarrow>
      \<Union>I \<in> C \<longrightarrow> m (\<Union>I) = (\<Sum>u\<in>I. m u))"

definition q2631152_sigma_subadditive ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> ennreal) \<Rightarrow> bool" where
  "q2631152_sigma_subadditive C m \<longleftrightarrow>
    (\<forall>F :: nat \<Rightarrow> 'a set.
      (\<forall>i. F i \<in> C) \<longrightarrow>
      (\<Union>i. F i) \<in> C \<longrightarrow>
      m (\<Union>i. F i) \<le> (\<Sum>i. m (F i)))"

definition q2631152_generated_measure ::
    "'a set set \<Rightarrow> 'a set set \<Rightarrow>
      ('a set \<Rightarrow> ennreal) \<Rightarrow> 'a measure" where
  "q2631152_generated_measure A C m =
    measure_of UNIV A (emeasure (extend_measure UNIV C id m))"

theorem q2631152_caratheodory_extension_agrees:
  fixes A C :: "'a set set"
    and m :: "'a set \<Rightarrow> ennreal"
    and s :: "'a set"
  assumes semiring: "q2631152_set_semiring C"
    and content: "q2631152_add_content C m"
    and sigma_subadditive: "q2631152_sigma_subadditive C m"
    and generated: "A = sigma_sets UNIV C"
    and hs: "s \<in> C"
  shows "emeasure (q2631152_generated_measure A C m) s = m s"
  sorry

end
