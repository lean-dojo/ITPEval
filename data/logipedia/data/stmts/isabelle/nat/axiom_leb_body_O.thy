(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_leb_body_O, catalog title "nat.axiom_leb_body_O": the source
  equality predicate relates the abstract Boolean less-than-or-equal body at
  zero to the constant-true function on natural numbers. This file contains
  no proof.
*)

theory axiom_leb_body_O
  imports Main
begin

consts
  logipedia_connectives_equal ::
    "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool"
  leb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"

theorem axiom_leb_body_O:
  "logipedia_connectives_equal
    (leb_body 0)
    (\<lambda>m :: nat. True)"
  sorry

end
