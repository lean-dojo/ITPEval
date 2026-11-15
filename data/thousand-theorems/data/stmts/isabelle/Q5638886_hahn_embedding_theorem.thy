(*
  Statement-only formalization of thousand-theorems corpus artifact Q5638886,
  "Hahn embedding theorem": every linearly ordered abelian group embeds
  injectively and order-preservingly into the lexicographically ordered group
  of real Hahn series indexed by its nonzero Archimedean classes, preserving
  the Archimedean class of every element. This file contains no proof.
*)

theory Q5638886_hahn_embedding_theorem
  imports Complex_Main
begin

primrec q5638886_nsmult ::
    "nat \<Rightarrow> 'a::linordered_ab_group_add \<Rightarrow> 'a" where
  "q5638886_nsmult 0 a = 0"
| "q5638886_nsmult (Suc n) a = q5638886_nsmult n a + a"

definition q5638886_abs ::
    "'a::linordered_ab_group_add \<Rightarrow> 'a" where
  "q5638886_abs a = (if 0 \<le> a then a else -a)"

definition q5638886_arch_equiv ::
    "'a::linordered_ab_group_add \<Rightarrow> 'a \<Rightarrow> bool" where
  "q5638886_arch_equiv a b \<longleftrightarrow>
    (\<exists>m. q5638886_abs b \<le> q5638886_nsmult m (q5638886_abs a)) \<and>
    (\<exists>n. q5638886_abs a \<le> q5638886_nsmult n (q5638886_abs b))"

definition q5638886_arch_class ::
    "'a::linordered_ab_group_add \<Rightarrow> 'a set" where
  "q5638886_arch_class a = {b. q5638886_arch_equiv a b}"

definition q5638886_finite_arch_classes ::
    "'a::linordered_ab_group_add set set" where
  "q5638886_finite_arch_classes =
    q5638886_arch_class ` {a. a \<noteq> 0}"

definition q5638886_arch_class_le ::
    "'a::linordered_ab_group_add set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q5638886_arch_class_le A B \<longleftrightarrow>
    (\<exists>a b.
      a \<noteq> 0 \<and> b \<noteq> 0 \<and>
      A = q5638886_arch_class a \<and>
      B = q5638886_arch_class b \<and>
      (\<exists>n.
        q5638886_abs b \<le> q5638886_nsmult n (q5638886_abs a)))"

definition q5638886_support ::
    "('a::linordered_ab_group_add set \<Rightarrow> real) \<Rightarrow> 'a set set" where
  "q5638886_support x =
    {A \<in> q5638886_finite_arch_classes. x A \<noteq> 0}"

definition q5638886_well_ordered_support ::
    "('a::linordered_ab_group_add set \<Rightarrow> real) \<Rightarrow> bool" where
  "q5638886_well_ordered_support x \<longleftrightarrow>
    (\<forall>S.
      S \<subseteq> q5638886_support x \<longrightarrow>
      S \<noteq> {} \<longrightarrow>
      (\<exists>A \<in> S. \<forall>B \<in> S. q5638886_arch_class_le A B))"

definition q5638886_hahn_series ::
    "('a::linordered_ab_group_add set \<Rightarrow> real) \<Rightarrow> bool" where
  "q5638886_hahn_series x \<longleftrightarrow>
    (\<forall>A. A \<notin> q5638886_finite_arch_classes \<longrightarrow> x A = 0) \<and>
    q5638886_well_ordered_support x"

definition q5638886_is_leading_class ::
    "('a::linordered_ab_group_add set \<Rightarrow> real) \<Rightarrow>
      'a set \<Rightarrow> bool" where
  "q5638886_is_leading_class x A \<longleftrightarrow>
    A \<in> q5638886_support x \<and>
    (\<forall>B \<in> q5638886_support x. q5638886_arch_class_le A B)"

definition q5638886_leading_arch_class ::
    "('a::linordered_ab_group_add set \<Rightarrow> real) \<Rightarrow> 'a set" where
  "q5638886_leading_arch_class x =
    (if x = (\<lambda>_. 0)
     then q5638886_arch_class 0
     else (THE A. q5638886_is_leading_class x A))"

definition q5638886_lex_le ::
    "('a::linordered_ab_group_add set \<Rightarrow> real) \<Rightarrow>
      ('a set \<Rightarrow> real) \<Rightarrow> bool" where
  "q5638886_lex_le x y \<longleftrightarrow>
    q5638886_hahn_series x \<and>
    q5638886_hahn_series y \<and>
    (x = y \<or>
      (\<exists>A.
        q5638886_is_leading_class (\<lambda>B. y B - x B) A \<and>
        x A < y A))"

definition q5638886_is_order_add_monoid_hom ::
    "('a::linordered_ab_group_add \<Rightarrow> 'a set \<Rightarrow> real) \<Rightarrow> bool" where
  "q5638886_is_order_add_monoid_hom f \<longleftrightarrow>
    (\<forall>a. q5638886_hahn_series (f a)) \<and>
    f 0 = (\<lambda>_. 0) \<and>
    (\<forall>a b A. f (a + b) A = f a A + f b A) \<and>
    (\<forall>a b. a \<le> b \<longrightarrow> q5638886_lex_le (f a) (f b))"

theorem hahnEmbedding_isOrderedAddMonoid:
  "\<exists>f :: 'a::linordered_ab_group_add \<Rightarrow> 'a set \<Rightarrow> real.
    q5638886_is_order_add_monoid_hom f \<and>
    inj f \<and>
    (\<forall>a. q5638886_arch_class a = q5638886_leading_arch_class (f a))"
  sorry

end
