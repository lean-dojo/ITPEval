(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_plus_body_O, catalog title "nat.axiom_plus_body_O": the source
  equality predicate relates the abstract natural-number addition body at
  zero to the identity function. This file contains no proof.
*)

theory axiom_plus_body_O
  imports Main
begin

consts
  logipedia_connectives_equal ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  plus_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_plus_body_O:
  "logipedia_connectives_equal
    (plus_body 0)
    (\<lambda>m :: nat. m)"
  sorry

end
