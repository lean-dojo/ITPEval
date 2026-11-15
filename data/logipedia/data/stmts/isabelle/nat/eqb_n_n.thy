(*
  Statement-only formalization of Logipedia corpus artifact nat.eqb_n_n,
  catalog title "nat.eqb_n_n": the Boolean equality test on a natural number
  and itself returns true. This file contains no proof.
*)

theory eqb_n_n
  imports Main
begin

fun eqb :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "eqb 0 0 = True"
| "eqb 0 (Suc m) = False"
| "eqb (Suc n) 0 = False"
| "eqb (Suc n) (Suc m) = eqb n m"

theorem eqb_n_n:
  "\<forall>n :: nat. eqb n n = True"
  sorry

end
