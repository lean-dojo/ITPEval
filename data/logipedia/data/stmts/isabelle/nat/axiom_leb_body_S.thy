(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_leb_body_S, catalog title "nat.axiom_leb_body_S": for every
  natural number, the source equality predicate relates the abstract Boolean
  less-than-or-equal body at its successor to the natural-number matcher that
  is false at zero and delegates to the preceding less-than-or-equal function
  on successors. This file contains no proof.
*)

theory axiom_leb_body_S
  imports Main
begin

consts
  logipedia_connectives_equal ::
    "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool"
  leb :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  leb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  match_nat_type_bool ::
    "bool \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool"

theorem axiom_leb_body_S:
  "\<forall>n :: nat.
    logipedia_connectives_equal
      (leb_body (Suc n))
      (\<lambda>m :: nat.
        match_nat_type_bool False (\<lambda>q :: nat. leb n q) m)"
  sorry

end
