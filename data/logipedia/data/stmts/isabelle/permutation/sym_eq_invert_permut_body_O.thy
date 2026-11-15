(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.sym_eq_invert_permut_body_O, catalog title
  "permutation.sym_eq_invert_permut_body_O": the function that, for every
  natural-valued function f and natural m, selects zero in either branch
  according to whether m equals f 0 is Leibniz-equal to the abstract
  inverse-permutation body at zero. This file contains no proof.
*)

theory sym_eq_invert_permut_body_O
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
  invert_permut_body ::
    "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_invert_permut_body_O:
  "logipedia_leibniz
    (\<lambda>f :: nat \<Rightarrow> nat. \<lambda>m :: nat.
      logipedia_match_bool_type 0 0 (m = f 0))
    (invert_permut_body 0)"
  sorry

end
