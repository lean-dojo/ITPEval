(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.eq_invert_permut_body_S, catalog title
  "permutation.eq_invert_permut_body_S": for every natural number, the
  abstract inverse-permutation body at its successor is Leibniz-equal to the
  function that returns that successor when m equals its image under f, and
  otherwise uses the preceding inverse-permutation function. This file
  contains no proof.
*)

theory eq_invert_permut_body_S
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

theorem eq_invert_permut_body_S:
  "\<forall>n :: nat.
    logipedia_leibniz
      (invert_permut_body (Suc n))
      (\<lambda>f :: nat \<Rightarrow> nat. \<lambda>m :: nat.
        logipedia_match_bool_type
          (Suc n)
          (invert_permut n f m)
          (m = f (Suc n)))"
  sorry

end
