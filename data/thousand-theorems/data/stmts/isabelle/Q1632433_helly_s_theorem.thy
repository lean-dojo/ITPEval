(*
  Statement-only formalization of thousand-theorems corpus artifact Q1632433,
  "Helly's theorem": for a finite family of convex sets in a finite-dimensional
  vector space over a linearly ordered field, if every subfamily of size one
  more than the dimension has nonempty intersection, then the entire family
  has nonempty intersection. This file contains no proof.
*)

theory Q1632433_helly_s_theorem
  imports Main
begin

definition q1632433_module ::
    "('k::field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1632433_module smult \<longleftrightarrow>
    (\<forall>a x y. smult a (x + y) = smult a x + smult a y) \<and>
    (\<forall>a b x. smult (a + b) x = smult a x + smult b x) \<and>
    (\<forall>a b x. smult (a * b) x = smult a (smult b x)) \<and>
    (\<forall>x. smult 1 x = x)"

definition q1632433_linear_independent ::
    "('k::field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
      'e set \<Rightarrow> bool" where
  "q1632433_linear_independent smult B \<longleftrightarrow>
    (\<forall>w :: 'e \<Rightarrow> 'k.
      finite {x. w x \<noteq> 0} \<longrightarrow>
      {x. w x \<noteq> 0} \<subseteq> B \<longrightarrow>
      (\<Sum>x\<in>{x. w x \<noteq> 0}. smult (w x) x) = 0 \<longrightarrow>
      (\<forall>x\<in>B. w x = 0))"

definition q1632433_spans ::
    "('k::field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
      'e set \<Rightarrow> bool" where
  "q1632433_spans smult B \<longleftrightarrow>
    (\<forall>x. \<exists>w :: 'e \<Rightarrow> 'k.
      finite {y. w y \<noteq> 0} \<and>
      {y. w y \<noteq> 0} \<subseteq> B \<and>
      (\<Sum>y\<in>{y. w y \<noteq> 0}. smult (w y) y) = x)"

definition q1632433_basis ::
    "('k::field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
      'e set \<Rightarrow> bool" where
  "q1632433_basis smult B \<longleftrightarrow>
    q1632433_linear_independent smult B \<and> q1632433_spans smult B"

definition q1632433_finite_dimensional ::
    "('k::field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1632433_finite_dimensional smult \<longleftrightarrow>
    (\<exists>B :: 'e set. finite B \<and> q1632433_basis smult B)"

definition q1632433_dimension ::
    "('k::field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow> nat" where
  "q1632433_dimension smult =
    (LEAST n. \<exists>B :: 'e set.
      finite B \<and> q1632433_basis smult B \<and> card B = n)"

definition q1632433_convex ::
    "('k::linordered_field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
      'e set \<Rightarrow> bool" where
  "q1632433_convex smult S \<longleftrightarrow>
    (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>a\<ge>0. \<forall>b\<ge>0.
      a + b = 1 \<longrightarrow> smult a x + smult b y \<in> S)"

theorem helly_theorem:
  fixes smult :: "'k::linordered_field \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e"
    and F :: "'i \<Rightarrow> 'e set"
    and s :: "'i set"
  assumes module: "q1632433_module smult"
    and finite_dimensional: "q1632433_finite_dimensional smult"
    and finite_family: "finite s"
    and family_large:
      "q1632433_dimension smult + 1 \<le> card s"
    and convex_family:
      "\<And>i. i \<in> s \<Longrightarrow> q1632433_convex smult (F i)"
    and small_intersections:
      "\<And>I. I \<subseteq> s \<Longrightarrow>
        card I = q1632433_dimension smult + 1 \<Longrightarrow>
        {x. \<forall>i\<in>I. x \<in> F i} \<noteq> {}"
  shows "{x. \<forall>i\<in>s. x \<in> F i} \<noteq> {}"
  sorry

end
