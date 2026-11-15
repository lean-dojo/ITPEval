(*
  Statement-only formalization of Logipedia corpus artifact nat.le_pred_n,
  catalog title "nat.le_pred_n": the predecessor of every natural number is
  less than or equal to that number. This file contains no proof.
*)

theory le_pred_n
  imports Main
begin

theorem le_pred_n:
  "\<forall>n :: nat. Nat.pred n \<le> n"
  sorry

end
