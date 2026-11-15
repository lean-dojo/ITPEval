(*
  Statement-only formalization of Logipedia corpus artifact nat.eqb_elim,
  catalog title "nat.eqb_elim": elimination for recursively computed
  natural-number Boolean equality by the equal and unequal cases. This file
  contains no proof.
*)

theory eqb_elim
  imports Main
begin

fun eqb :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "eqb 0 0 = True"
| "eqb 0 (Suc m) = False"
| "eqb (Suc n) 0 = False"
| "eqb (Suc n) (Suc m) = eqb n m"

theorem eqb_elim:
  "\<forall>n m :: nat.
    \<forall>P :: bool \<Rightarrow> bool.
      (n = m \<longrightarrow> P True) \<longrightarrow>
      (\<not> (n = m) \<longrightarrow> P False) \<longrightarrow>
      P (eqb n m)"
  sorry

end
