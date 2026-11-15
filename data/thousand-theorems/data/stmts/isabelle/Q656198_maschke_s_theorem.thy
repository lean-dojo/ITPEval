(*
  Statement-only formalization of thousand-theorems corpus artifact Q656198
  (thousand-theorems__isabelle__Q656198), "Maschke's theorem": for a finite
  group over a field in which the group cardinality is nonzero, every
  submodule of a module over the group algebra has a complementary submodule.
  This file contains no proof.
*)

theory Q656198_maschke_s_theorem
  imports Main
begin

definition q656198_group_algebra_zero ::
    "'g \<Rightarrow> 'k::field" where
  "q656198_group_algebra_zero = (\<lambda>_. 0)"

definition q656198_group_algebra_one ::
    "'g::{finite,group_add} \<Rightarrow> 'k::field" where
  "q656198_group_algebra_one =
    (\<lambda>g. if g = 0 then 1 else 0)"

definition q656198_group_algebra_add ::
    "('g \<Rightarrow> 'k::field) \<Rightarrow> ('g \<Rightarrow> 'k) \<Rightarrow>
      'g \<Rightarrow> 'k" where
  "q656198_group_algebra_add a b = (\<lambda>g. a g + b g)"

definition q656198_group_algebra_mul ::
    "('g::{finite,group_add} \<Rightarrow> 'k::field) \<Rightarrow>
      ('g \<Rightarrow> 'k) \<Rightarrow> 'g \<Rightarrow> 'k" where
  "q656198_group_algebra_mul a b =
    (\<lambda>x. \<Sum>g\<in>UNIV. a g * b (-g + x))"

definition q656198_group_algebra_module ::
    "(('g::{finite,group_add} \<Rightarrow> 'k::field) \<Rightarrow>
      'v::ab_group_add \<Rightarrow> 'v) \<Rightarrow> bool" where
  "q656198_group_algebra_module smul \<longleftrightarrow>
    (\<forall>v. smul q656198_group_algebra_one v = v) \<and>
    (\<forall>a b v.
      smul (q656198_group_algebra_mul a b) v = smul a (smul b v)) \<and>
    (\<forall>a b v.
      smul (q656198_group_algebra_add a b) v = smul a v + smul b v) \<and>
    (\<forall>a v w. smul a (v + w) = smul a v + smul a w) \<and>
    (\<forall>v. smul q656198_group_algebra_zero v = 0) \<and>
    (\<forall>a. smul a 0 = 0)"

definition q656198_submodule ::
    "(('g::{finite,group_add} \<Rightarrow> 'k::field) \<Rightarrow>
      'v::ab_group_add \<Rightarrow> 'v) \<Rightarrow> 'v set \<Rightarrow> bool" where
  "q656198_submodule smul P \<longleftrightarrow>
    0 \<in> P \<and>
    (\<forall>v\<in>P. -v \<in> P) \<and>
    (\<forall>v\<in>P. \<forall>w\<in>P. v + w \<in> P) \<and>
    (\<forall>a. \<forall>v\<in>P. smul a v \<in> P)"

definition q656198_are_complements ::
    "'v::ab_group_add set \<Rightarrow> 'v set \<Rightarrow> bool" where
  "q656198_are_complements P Q \<longleftrightarrow>
    P \<inter> Q = {0} \<and>
    (\<forall>v. \<exists>p\<in>P. \<exists>q\<in>Q. v = p + q)"

theorem q656198_maschke_s_theorem:
  fixes smul ::
      "('g::{finite,group_add} \<Rightarrow> 'k::field) \<Rightarrow>
        'v::ab_group_add \<Rightarrow> 'v"
    and P :: "'v set"
  assumes cardinality_nonzero:
      "(of_nat (card (UNIV :: 'g set)) :: 'k) \<noteq> 0"
    and module:
      "q656198_group_algebra_module smul"
    and submodule:
      "q656198_submodule smul P"
  shows "\<exists>Q.
    q656198_submodule smul Q \<and>
    q656198_are_complements P Q"
  sorry

end
