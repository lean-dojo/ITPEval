(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_times_body_O, catalog title "nat.axiom_times_body_O": the abstract
  natural-number multiplication body at zero is related by the source equality
  predicate to the constant-zero function. This file contains no proof.
*)

theory axiom_times_body_O
  imports Main
begin

consts
  logipedia_connectives_equal ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  times_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_times_body_O:
  "logipedia_connectives_equal
    (times_body 0)
    (\<lambda>m :: nat. 0)"
  sorry

end
