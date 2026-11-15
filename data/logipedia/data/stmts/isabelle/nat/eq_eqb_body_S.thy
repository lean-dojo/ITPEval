(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_eqb_body_S, catalog title "nat.eq_eqb_body_S": for every natural
  number, the abstract Boolean equality body at its successor is
  Leibniz-equal to the natural-number matcher that is false at zero and
  delegates to the preceding equality function on successors. This file
  contains no proof.
*)

theory eq_eqb_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  eqb :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  eqb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  match_nat_type_bool ::
    "bool \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool"

theorem eq_eqb_body_S:
  "\<forall>n :: nat.
    logipedia_leibniz
      (eqb_body (Suc n))
      (\<lambda>m :: nat.
        match_nat_type_bool False (\<lambda>q :: nat. eqb n q) m)"
  sorry

end
