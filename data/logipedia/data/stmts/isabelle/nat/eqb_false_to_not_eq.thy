(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eqb_false_to_not_eq, catalog title "nat.eqb_false_to_not_eq": Boolean
  equality of two natural numbers returning false implies that the natural
  numbers are unequal. This file contains no proof.
*)

theory eqb_false_to_not_eq
  imports Main
begin

fun eqb :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "eqb 0 0 = True"
| "eqb 0 (Suc m) = False"
| "eqb (Suc n) 0 = False"
| "eqb (Suc n) (Suc m) = eqb n m"

theorem eqb_false_to_not_eq:
  "\<forall>n m :: nat. eqb n m = False \<longrightarrow> \<not> (n = m)"
  sorry

end
