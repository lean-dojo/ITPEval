(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q3526996, "Kolmogorov extension theorem": every projective family of finite
  measures on the finite products of Polish coordinate spaces has a measure
  on the full dependent product with exactly those finite-dimensional
  marginals. This file contains no proof.
*)

theory Q3526996_kolmogorov_extension_theorem
  imports "HOL.Complex_Main"
begin

type_synonym 'a q3526996_measurable_space = "'a set \<times> 'a set set"
type_synonym 'a q3526996_finite_measure = "'a set \<Rightarrow> real"

definition q3526996_space ::
    "'a q3526996_measurable_space \<Rightarrow> 'a set" where
  "q3526996_space M = fst M"

definition q3526996_sets ::
    "'a q3526996_measurable_space \<Rightarrow> 'a set set" where
  "q3526996_sets M = snd M"

definition q3526996_sigma_field ::
    "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "q3526996_sigma_field \<Omega> A \<longleftrightarrow>
    A \<subseteq> Pow \<Omega> \<and>
    {} \<in> A \<and>
    (\<forall>E \<in> A. \<Omega> - E \<in> A) \<and>
    (\<forall>E :: nat \<Rightarrow> 'a set.
      (\<forall>n. E n \<in> A) \<longrightarrow> (\<Union>n. E n) \<in> A)"

definition q3526996_generated ::
    "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
  "q3526996_generated \<Omega> G =
    \<Inter>{A. q3526996_sigma_field \<Omega> A \<and> G \<subseteq> A}"

definition q3526996_measurable_space ::
    "'a q3526996_measurable_space \<Rightarrow> bool" where
  "q3526996_measurable_space M \<longleftrightarrow>
    q3526996_sigma_field (q3526996_space M) (q3526996_sets M)"

definition q3526996_real_borel_sets :: "real set set" where
  "q3526996_real_borel_sets =
    q3526996_generated UNIV {U :: real set. open U}"

definition q3526996_standard_borel_space ::
    "'a q3526996_measurable_space \<Rightarrow> bool" where
  "q3526996_standard_borel_space M \<longleftrightarrow>
    q3526996_measurable_space M \<and>
    (\<exists>code :: 'a \<Rightarrow> real.
      inj_on code (q3526996_space M) \<and>
      code ` q3526996_space M \<in> q3526996_real_borel_sets \<and>
      (\<forall>A.
        A \<in> q3526996_sets M \<longleftrightarrow>
        A \<subseteq> q3526996_space M \<and>
        (\<exists>B \<in> q3526996_real_borel_sets.
          A = q3526996_space M \<inter> code -` B)))"

definition q3526996_pie ::
    "'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow> 'a) set" where
  "q3526996_pie I X =
    {x. (\<forall>i \<in> I. x i \<in> X i) \<and>
      (\<forall>i. i \<notin> I \<longrightarrow> x i = undefined)}"

definition q3526996_restrict ::
    "('i \<Rightarrow> 'a) \<Rightarrow> 'i set \<Rightarrow> ('i \<Rightarrow> 'a)" where
  "q3526996_restrict x I =
    (\<lambda>i. if i \<in> I then x i else undefined)"

definition q3526996_product_space ::
    "'i set \<Rightarrow> ('i \<Rightarrow> 'a q3526996_measurable_space) \<Rightarrow>
     ('i \<Rightarrow> 'a) q3526996_measurable_space" where
  "q3526996_product_space I M =
    (q3526996_pie I (\<lambda>i. q3526996_space (M i)),
     q3526996_generated
       (q3526996_pie I (\<lambda>i. q3526996_space (M i)))
       {C. \<exists>i \<in> I. \<exists>E \<in> q3526996_sets (M i).
         C = {x \<in> q3526996_pie I
           (\<lambda>j. q3526996_space (M j)). x i \<in> E}})"

definition q3526996_is_finite_measure ::
    "'a q3526996_measurable_space \<Rightarrow>
     'a q3526996_finite_measure \<Rightarrow> bool" where
  "q3526996_is_finite_measure M \<mu> \<longleftrightarrow>
    q3526996_measurable_space M \<and>
    (\<forall>E. \<mu> E = \<mu> (E \<inter> q3526996_space M)) \<and>
    \<mu> {} = 0 \<and>
    (\<forall>E \<in> q3526996_sets M. 0 \<le> \<mu> E) \<and>
    (\<forall>E :: nat \<Rightarrow> 'a set.
      (\<forall>n. E n \<in> q3526996_sets M) \<and>
      (\<forall>i j. i \<noteq> j \<longrightarrow> E i \<inter> E j = {})
      \<longrightarrow>
      summable (\<lambda>n. \<mu> (E n)) \<and>
      \<mu> (\<Union>n. E n) = suminf (\<lambda>n. \<mu> (E n)))"

definition q3526996_pushforward ::
    "'a q3526996_measurable_space \<Rightarrow>
     'b q3526996_measurable_space \<Rightarrow>
     ('a \<Rightarrow> 'b) \<Rightarrow>
     'a q3526996_finite_measure \<Rightarrow>
     'b q3526996_finite_measure" where
  "q3526996_pushforward A B f \<mu> E =
    \<mu> {x \<in> q3526996_space A.
      f x \<in> E \<inter> q3526996_space B}"

definition q3526996_projective_measure_family ::
    "('i \<Rightarrow> 'a q3526996_measurable_space) \<Rightarrow>
     ('i set \<Rightarrow> ('i \<Rightarrow> 'a) q3526996_finite_measure) \<Rightarrow>
     bool" where
  "q3526996_projective_measure_family M P \<longleftrightarrow>
    (\<forall>J. finite J \<longrightarrow>
      q3526996_is_finite_measure
        (q3526996_product_space J M) (P J)) \<and>
    (\<forall>J K. J \<subseteq> K \<longrightarrow> finite K \<longrightarrow>
      (\<forall>E \<in> q3526996_sets (q3526996_product_space J M).
        P J E =
          q3526996_pushforward
            (q3526996_product_space K M)
            (q3526996_product_space J M)
            (\<lambda>x. q3526996_restrict x J) (P K) E))"

definition q3526996_is_projective_limit ::
    "('i \<Rightarrow> 'a q3526996_measurable_space) \<Rightarrow>
     ('i set \<Rightarrow> ('i \<Rightarrow> 'a) q3526996_finite_measure) \<Rightarrow>
     ('i \<Rightarrow> 'a) q3526996_finite_measure \<Rightarrow> bool" where
  "q3526996_is_projective_limit M P \<mu> \<longleftrightarrow>
    q3526996_is_finite_measure
      (q3526996_product_space UNIV M) \<mu> \<and>
    (\<forall>J. finite J \<longrightarrow>
      (\<forall>E \<in> q3526996_sets (q3526996_product_space J M).
        q3526996_pushforward
          (q3526996_product_space UNIV M)
          (q3526996_product_space J M)
          (\<lambda>x. q3526996_restrict x J) \<mu> E = P J E))"

definition q3526996_projective_limit ::
    "('i \<Rightarrow> 'a q3526996_measurable_space) \<Rightarrow>
     ('i set \<Rightarrow> ('i \<Rightarrow> 'a) q3526996_finite_measure) \<Rightarrow>
     ('i \<Rightarrow> 'a) q3526996_finite_measure" where
  "q3526996_projective_limit M P =
    (SOME \<mu>. q3526996_is_projective_limit M P \<mu>)"

theorem kolmogorov_extension_theorem:
  fixes M :: "'i \<Rightarrow> 'a q3526996_measurable_space"
    and P ::
      "'i set \<Rightarrow> ('i \<Rightarrow> 'a) q3526996_finite_measure"
  assumes polish_coordinates:
      "\<forall>i. q3526996_standard_borel_space (M i)"
    and projective:
      "q3526996_projective_measure_family M P"
  shows
      "q3526996_is_projective_limit M P
        (q3526996_projective_limit M P)"
  sorry

end
