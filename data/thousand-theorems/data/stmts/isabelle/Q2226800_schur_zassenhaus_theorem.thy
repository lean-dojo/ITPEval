(*
  Statement-only formalization of thousand-theorems corpus artifact Q2226800
  (thousand-theorems__isabelle__Q2226800),
  "Schur–Zassenhaus theorem": a normal subgroup whose order is coprime to its
  index has a subgroup forming a left complement with unique factorization.
  This file contains no proof.
*)

theory Q2226800_schur_zassenhaus_theorem
  imports Main
begin

definition q2226800_is_subgroup :: "'g::group_add set \<Rightarrow> bool" where
  "q2226800_is_subgroup H \<longleftrightarrow>
    0 \<in> H \<and>
    (\<forall>x \<in> H. -x \<in> H) \<and>
    (\<forall>x \<in> H. \<forall>y \<in> H. x + y \<in> H)"

definition q2226800_is_normal_subgroup :: "'g::group_add set \<Rightarrow> bool" where
  "q2226800_is_normal_subgroup N \<longleftrightarrow>
    q2226800_is_subgroup N \<and>
    (\<forall>g. \<forall>n \<in> N. g + n + (-g) \<in> N)"

definition q2226800_right_cosets :: "'g::group_add set \<Rightarrow> 'g set set" where
  "q2226800_right_cosets N =
    (\<lambda>g. (\<lambda>n. n + g) ` N) ` UNIV"

definition q2226800_subgroup_index :: "'g::group_add set \<Rightarrow> nat" where
  "q2226800_subgroup_index N = card (q2226800_right_cosets N)"

definition q2226800_is_left_complement ::
    "'g::group_add set \<Rightarrow> 'g set \<Rightarrow> bool" where
  "q2226800_is_left_complement H N \<longleftrightarrow>
    q2226800_is_subgroup H \<and>
    q2226800_is_subgroup N \<and>
    bij_betw (\<lambda>(h, n). h + n) (H \<times> N) UNIV"

theorem q2226800_schur_zassenhaus:
  fixes N :: "'g::group_add set"
  assumes normal_N: "q2226800_is_normal_subgroup N"
    and coprime_order_index:
      "coprime (card N) (q2226800_subgroup_index N)"
  shows "\<exists>H :: 'g set. q2226800_is_left_complement H N"
  sorry

end
