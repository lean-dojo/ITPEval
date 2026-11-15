(*
  Statement-only formalization of Logipedia corpus artifact
  nat.leb_true_to_le, catalog title "nat.leb_true_to_le": if the recursive
  Boolean less-than-or-equal test on two natural numbers returns true, then
  the first number is at most the second. This file contains no proof.
*)

theory leb_true_to_le
  imports Main
begin

fun leb :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "leb 0 m = True"
| "leb (Suc n) 0 = False"
| "leb (Suc n) (Suc m) = leb n m"

theorem leb_true_to_le:
  "\<forall>n m :: nat. leb n m = True \<longrightarrow> n \<le> m"
  sorry

end
