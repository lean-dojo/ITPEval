(*
  Statement-only formalization of thousand-theorems corpus artifact Q1187646
  (thousand-theorems__isabelle__Q1187646), "Fundamental theorem on
  homomorphisms": every group homomorphism canonically identifies the quotient
  by its kernel with its range as a group. This file contains no proof.
*)

theory Q1187646_fundamental_theorem_on_homomorphisms
  imports Main
begin

definition q1187646_is_group_hom ::
    "('g::group_add \<Rightarrow> 'h::group_add) \<Rightarrow> bool" where
  "q1187646_is_group_hom f \<longleftrightarrow>
    f 0 = 0 \<and> (\<forall>x y. f (x + y) = f x + f y)"

definition q1187646_hom_kernel ::
    "('g::group_add \<Rightarrow> 'h::group_add) \<Rightarrow> 'g set" where
  "q1187646_hom_kernel f = {x. f x = 0}"

definition q1187646_hom_range ::
    "('g::group_add \<Rightarrow> 'h::group_add) \<Rightarrow> 'h set" where
  "q1187646_hom_range f = f ` UNIV"

definition q1187646_left_coset ::
    "'g::group_add set \<Rightarrow> 'g \<Rightarrow> 'g set" where
  "q1187646_left_coset N g = (\<lambda>n. n + g) ` N"

definition q1187646_quotient_carrier ::
    "'g::group_add set \<Rightarrow> 'g set set" where
  "q1187646_quotient_carrier N = q1187646_left_coset N ` UNIV"

definition q1187646_coset_add ::
    "'g::group_add set \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "q1187646_coset_add X Y =
    {x + y |x y. x \<in> X \<and> y \<in> Y}"

theorem q1187646_quotientKerEquivRange:
  fixes phi :: "'g::group_add \<Rightarrow> 'h::group_add"
  assumes "q1187646_is_group_hom phi"
  shows "\<exists>F :: 'g set \<Rightarrow> 'h.
    bij_betw F
      (q1187646_quotient_carrier (q1187646_hom_kernel phi))
      (q1187646_hom_range phi) \<and>
    (\<forall>g.
      F (q1187646_left_coset (q1187646_hom_kernel phi) g) = phi g) \<and>
    (\<forall>X \<in> q1187646_quotient_carrier (q1187646_hom_kernel phi).
      \<forall>Y \<in> q1187646_quotient_carrier (q1187646_hom_kernel phi).
        F (q1187646_coset_add X Y) = F X + F Y)"
  sorry

end
