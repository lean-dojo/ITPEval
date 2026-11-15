(*
  Statement-only formalization of Logipedia corpus artifact nat.le_S,
  catalog title "nat.le_S": natural-number order is preserved when the upper
  bound is replaced by its successor. This file contains no proof.
*)

theory le_S
  imports Main
begin

theorem le_S:
  "\<forall>n m :: nat. n \<le> m \<longrightarrow> n \<le> Suc m"
  sorry

end
