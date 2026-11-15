(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.sym_eq_invert_permut_body_S, catalog title
  "permutation.sym_eq_invert_permut_body_S": for every natural number, the
  function that returns its successor when m equals its image under f, and
  otherwise uses the preceding inverse-permutation function, is
  Leibniz-equal to the abstract inverse-permutation body at that successor.
  This file contains no proof.
*)

theory sym_eq_invert_permut_body_S
  imports Main
begin

definition logipedia_match_bool_type ::
  "'a \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a"
where
  "logipedia_match_bool_type case_true case_false b =
    (if b then case_true else case_false)"

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  invert_permut :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
  invert_permut_body ::
    "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_invert_permut_body_S:
  "\<forall>n :: nat.
    logipedia_leibniz
      (\<lambda>f :: nat \<Rightarrow> nat. \<lambda>m :: nat.
        logipedia_match_bool_type
          (Suc n)
          (invert_permut n f m)
          (m = f (Suc n)))
      (invert_permut_body (Suc n))"
  sorry

end
