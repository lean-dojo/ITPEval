(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.axiom_invert_permut_body_O, catalog title
  "permutation.axiom_invert_permut_body_O": the source equality predicate
  relates the abstract inverse-permutation body at zero to the function that,
  for every natural-valued function f and natural m, selects zero in either
  branch according to whether m equals f 0. This file contains no proof.
*)

theory axiom_invert_permut_body_O
  imports Main
begin

definition logipedia_match_bool_type ::
  "'a \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a"
where
  "logipedia_match_bool_type case_true case_false b =
    (if b then case_true else case_false)"

consts
  logipedia_connectives_equal ::
    "((nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
      ((nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> bool"
  invert_permut_body ::
    "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_invert_permut_body_O:
  "logipedia_connectives_equal
    (invert_permut_body 0)
    (\<lambda>f :: nat \<Rightarrow> nat. \<lambda>m :: nat.
      logipedia_match_bool_type 0 0 (m = f 0))"
  sorry

end
