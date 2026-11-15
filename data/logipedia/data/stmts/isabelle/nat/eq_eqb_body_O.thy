(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_eqb_body_O, catalog title "nat.eq_eqb_body_O": the abstract Boolean
  equality body at zero is Leibniz-equal to the natural-number matcher with
  true and false branches. This file contains no proof.
*)

theory eq_eqb_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  eqb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  match_nat_type_bool ::
    "bool \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool"

theorem eq_eqb_body_O:
  "logipedia_leibniz
    (eqb_body 0 :: nat \<Rightarrow> bool)
    (\<lambda>m :: nat.
      match_nat_type_bool True (\<lambda>q :: nat. False) m)"
  sorry

end
