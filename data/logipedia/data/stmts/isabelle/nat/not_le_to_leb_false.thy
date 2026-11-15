(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_le_to_leb_false, catalog title nat.not_le_to_leb_false: for natural
  numbers, failure of the inductive less-than-or-equal relation forces its
  recursive Boolean decision function to return False. This file contains no
  proof.
*)

theory not_le_to_leb_false
  imports Main
begin

fun logipedia_leb :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "logipedia_leb 0 m = True"
| "logipedia_leb (Suc n) 0 = False"
| "logipedia_leb (Suc n) (Suc m) = logipedia_leb n m"

theorem not_le_to_leb_false:
  "\<forall>n :: nat. \<forall>m :: nat.
    \<not> n \<le> m \<longrightarrow> logipedia_leb n m = False"
  sorry

end
