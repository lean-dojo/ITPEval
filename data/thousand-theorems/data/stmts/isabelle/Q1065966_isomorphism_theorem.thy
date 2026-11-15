(*
  Statement-only formalization of thousand-theorems corpus artifact Q1065966,
  "Isomorphism theorem": the canonical first, second, and third isomorphism
  theorems for arbitrary groups and their normal-subgroup quotients. This file
  contains no proof.
*)

theory Q1065966_isomorphism_theorem
  imports Main
begin

definition q1065966_is_subgroup :: "'g::group_add set \<Rightarrow> bool" where
  "q1065966_is_subgroup H \<longleftrightarrow>
    0 \<in> H \<and>
    (\<forall>x \<in> H. -x \<in> H) \<and>
    (\<forall>x \<in> H. \<forall>y \<in> H. x + y \<in> H)"

definition q1065966_is_normal_subgroup ::
    "'g::group_add set \<Rightarrow> bool" where
  "q1065966_is_normal_subgroup N \<longleftrightarrow>
    q1065966_is_subgroup N \<and>
    (\<forall>g. \<forall>n \<in> N. g + n + (-g) \<in> N)"

definition q1065966_is_group_hom ::
    "('g::group_add \<Rightarrow> 'h::group_add) \<Rightarrow> bool" where
  "q1065966_is_group_hom f \<longleftrightarrow>
    f 0 = 0 \<and> (\<forall>x y. f (x + y) = f x + f y)"

definition q1065966_hom_kernel ::
    "('g::group_add \<Rightarrow> 'h::group_add) \<Rightarrow> 'g set" where
  "q1065966_hom_kernel f = {x. f x = 0}"

definition q1065966_hom_range ::
    "('g::group_add \<Rightarrow> 'h::group_add) \<Rightarrow> 'h set" where
  "q1065966_hom_range f = f ` UNIV"

definition q1065966_left_coset ::
    "'g::group_add set \<Rightarrow> 'g \<Rightarrow> 'g set" where
  "q1065966_left_coset N g = (\<lambda>n. n + g) ` N"

definition q1065966_quotient_carrier ::
    "'g::group_add set \<Rightarrow> 'g set \<Rightarrow> 'g set set" where
  "q1065966_quotient_carrier A N = q1065966_left_coset N ` A"

definition q1065966_coset_mult ::
    "'g::group_add set \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "q1065966_coset_mult X Y =
    {x + y |x y. x \<in> X \<and> y \<in> Y}"

definition q1065966_subgroup_join ::
    "'g::group_add set \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "q1065966_subgroup_join H N =
    {x. \<forall>K. q1065966_is_subgroup K \<longrightarrow>
      H \<subseteq> K \<longrightarrow> N \<subseteq> K \<longrightarrow> x \<in> K}"

definition q1065966_quotient_image ::
    "'g::group_add set \<Rightarrow> 'g set \<Rightarrow> 'g set set" where
  "q1065966_quotient_image N M = q1065966_left_coset N ` M"

definition q1065966_quotient_left_coset ::
    "'g::group_add set set \<Rightarrow> 'g set \<Rightarrow> 'g set set" where
  "q1065966_quotient_left_coset S X =
    (\<lambda>A. q1065966_coset_mult A X) ` S"

definition q1065966_double_quotient_element ::
    "'g::group_add set \<Rightarrow> 'g set \<Rightarrow> 'g \<Rightarrow> 'g set set" where
  "q1065966_double_quotient_element N M g =
    q1065966_quotient_left_coset
      (q1065966_quotient_image N M)
      (q1065966_left_coset N g)"

definition q1065966_double_quotient_carrier ::
    "'g::group_add set \<Rightarrow> 'g set \<Rightarrow> 'g set set set" where
  "q1065966_double_quotient_carrier N M =
    q1065966_quotient_left_coset (q1065966_quotient_image N M) `
      q1065966_quotient_carrier UNIV N"

definition q1065966_quotient_coset_mult ::
    "'g::group_add set set \<Rightarrow> 'g set set \<Rightarrow> 'g set set" where
  "q1065966_quotient_coset_mult X Y =
    {q1065966_coset_mult A B |A B. A \<in> X \<and> B \<in> Y}"

theorem q1065966_quotientKerEquivRange:
  fixes phi :: "'g::group_add \<Rightarrow> 'h::group_add"
  assumes "q1065966_is_group_hom phi"
  shows "\<exists>F :: 'g set \<Rightarrow> 'h.
    bij_betw F
      (q1065966_quotient_carrier UNIV (q1065966_hom_kernel phi))
      (q1065966_hom_range phi) \<and>
    (\<forall>g. F (q1065966_left_coset (q1065966_hom_kernel phi) g) = phi g) \<and>
    (\<forall>X \<in> q1065966_quotient_carrier UNIV (q1065966_hom_kernel phi).
      \<forall>Y \<in> q1065966_quotient_carrier UNIV (q1065966_hom_kernel phi).
        F (q1065966_coset_mult X Y) = F X + F Y)"
  sorry

theorem q1065966_quotientInfEquivProdNormalQuotient:
  fixes H N :: "'g::group_add set"
  assumes "q1065966_is_subgroup H"
    and "q1065966_is_normal_subgroup N"
  shows "\<exists>F :: 'g set \<Rightarrow> 'g set.
    bij_betw F
      (q1065966_quotient_carrier H (H \<inter> N))
      (q1065966_quotient_carrier (q1065966_subgroup_join H N) N) \<and>
    (\<forall>h \<in> H.
      F (q1065966_left_coset (H \<inter> N) h) =
        q1065966_left_coset N h) \<and>
    (\<forall>X \<in> q1065966_quotient_carrier H (H \<inter> N).
      \<forall>Y \<in> q1065966_quotient_carrier H (H \<inter> N).
        F (q1065966_coset_mult X Y) =
          q1065966_coset_mult (F X) (F Y))"
  sorry

theorem q1065966_quotientQuotientEquivQuotient:
  fixes N M :: "'g::group_add set"
  assumes "q1065966_is_normal_subgroup N"
    and "q1065966_is_normal_subgroup M"
    and "N \<subseteq> M"
  shows "\<exists>F :: 'g set set \<Rightarrow> 'g set.
    bij_betw F
      (q1065966_double_quotient_carrier N M)
      (q1065966_quotient_carrier UNIV M) \<and>
    (\<forall>g.
      F (q1065966_double_quotient_element N M g) =
        q1065966_left_coset M g) \<and>
    (\<forall>X \<in> q1065966_double_quotient_carrier N M.
      \<forall>Y \<in> q1065966_double_quotient_carrier N M.
        F (q1065966_quotient_coset_mult X Y) =
          q1065966_coset_mult (F X) (F Y))"
  sorry

end
