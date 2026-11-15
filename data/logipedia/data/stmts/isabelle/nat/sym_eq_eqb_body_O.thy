(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_eqb_body_O, catalog title "nat.sym_eq_eqb_body_O": the
  natural-number matcher with true and false branches is Leibniz-equal to the
  abstract Boolean equality body at zero. This file contains no proof.
*)

theory sym_eq_eqb_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  eqb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  match_nat_type_bool ::
    "bool \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool"

theorem sym_eq_eqb_body_O:
  "logipedia_leibniz
    (\<lambda>m :: nat.
      match_nat_type_bool True (\<lambda>q :: nat. False) m)
    (eqb_body 0 :: nat \<Rightarrow> bool)"
  sorry

end
