(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_eqb_body_O, catalog title "nat.axiom_eqb_body_O": the source
  equality predicate relates the abstract Boolean equality body at zero to
  the natural-number matcher with true and false branches. This file contains
  no proof.
*)

theory axiom_eqb_body_O
  imports Main
begin

consts
  logipedia_connectives_equal ::
    "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool"
  eqb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  match_nat_type_bool ::
    "bool \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool"

theorem axiom_eqb_body_O:
  "logipedia_connectives_equal
    (eqb_body 0)
    (\<lambda>m :: nat.
      match_nat_type_bool True (\<lambda>q :: nat. False) m)"
  sorry

end
