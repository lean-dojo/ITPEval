(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.axiom_invert_permut_body_S, catalog title
  "permutation.axiom_invert_permut_body_S": for every natural number, the
  source equality predicate relates the abstract inverse-permutation body at
  its successor to the function that returns that successor when m equals its
  image under f, and otherwise uses the preceding inverse-permutation
  function. This file contains no proof.
*)

theory axiom_invert_permut_body_S
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
  invert_permut :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
  invert_permut_body ::
    "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_invert_permut_body_S:
  "\<forall>n :: nat.
    logipedia_connectives_equal
      (invert_permut_body (Suc n))
      (\<lambda>f :: nat \<Rightarrow> nat. \<lambda>m :: nat.
        logipedia_match_bool_type
          (Suc n)
          (invert_permut n f m)
          (m = f (Suc n)))"
  sorry

end
