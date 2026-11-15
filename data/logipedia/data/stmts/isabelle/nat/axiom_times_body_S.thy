(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_times_body_S, catalog title "nat.axiom_times_body_S": for every
  natural number, the source equality predicate relates the abstract
  multiplication body at its successor to the function mapping each natural
  number to its sum with the preceding multiplication value. This file
  contains no proof.
*)

theory axiom_times_body_S
  imports Main
begin

consts
  logipedia_connectives_equal ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  plus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  times :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  times_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_times_body_S:
  "\<forall>n :: nat.
    logipedia_connectives_equal
      (times_body (Suc n))
      (\<lambda>m :: nat. plus m (times n m))"
  sorry

end
