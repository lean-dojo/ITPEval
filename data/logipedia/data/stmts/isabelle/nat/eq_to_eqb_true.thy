(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_to_eqb_true, catalog title "nat.eq_to_eqb_true": equality of two
  natural numbers implies that their Boolean equality test is true. This file
  contains no proof.
*)

theory eq_to_eqb_true
  imports Main
begin

consts
  eqb :: "nat \<Rightarrow> nat \<Rightarrow> bool"

theorem eq_to_eqb_true:
  "\<forall>n m :: nat. n = m \<longrightarrow> eqb n m = True"
  sorry

end
