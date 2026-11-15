(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_plus_body_S, catalog title "nat.axiom_plus_body_S": for every
  natural number, the source equality predicate relates the abstract
  natural-number addition body at its successor to the function mapping each
  natural number to the successor of its sum with the original number. This
  file contains no proof.
*)

theory axiom_plus_body_S
  imports Main
begin

consts
  logipedia_connectives_equal ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  plus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  plus_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_plus_body_S:
  "\<forall>n :: nat.
    logipedia_connectives_equal
      (plus_body (Suc n))
      (\<lambda>m :: nat. Suc (plus n m))"
  sorry

end
