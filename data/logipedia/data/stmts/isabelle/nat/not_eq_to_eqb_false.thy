(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_eq_to_eqb_false, catalog title "nat.not_eq_to_eqb_false": unequal
  natural numbers have a Boolean equality test that returns false. This file
  contains no proof.
*)

theory not_eq_to_eqb_false
  imports Main
begin

fun eqb :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "eqb 0 0 = True"
| "eqb 0 (Suc m) = False"
| "eqb (Suc n) 0 = False"
| "eqb (Suc n) (Suc m) = eqb n m"

theorem not_eq_to_eqb_false:
  "\<forall>n m :: nat. n \<noteq> m \<longrightarrow> eqb n m = False"
  sorry

end
