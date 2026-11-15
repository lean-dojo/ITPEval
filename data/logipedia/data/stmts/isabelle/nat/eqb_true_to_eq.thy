(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eqb_true_to_eq, catalog title "nat.eqb_true_to_eq": if the recursive
  Boolean equality test for two natural numbers returns true, then the
  numbers are equal. This file contains no proof.
*)

theory eqb_true_to_eq
  imports Main
begin

fun eqb :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "eqb 0 0 = True"
| "eqb 0 (Suc m) = False"
| "eqb (Suc n) 0 = False"
| "eqb (Suc n) (Suc m) = eqb n m"

theorem eqb_true_to_eq:
  "\<forall>n m :: nat. eqb n m = True \<longrightarrow> n = m"
  sorry

end
