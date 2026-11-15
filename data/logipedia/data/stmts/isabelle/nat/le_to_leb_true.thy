(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_to_leb_true, catalog title "nat.le_to_leb_true": if one natural
  number is at most another, their recursive Boolean less-than-or-equal test
  returns true. This file contains no proof.
*)

theory le_to_leb_true
  imports Main
begin

fun leb :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "leb 0 m = True"
| "leb (Suc n) 0 = False"
| "leb (Suc n) (Suc m) = leb n m"

theorem le_to_leb_true:
  "\<forall>n m :: nat. n \<le> m \<longrightarrow> leb n m = True"
  sorry

end
