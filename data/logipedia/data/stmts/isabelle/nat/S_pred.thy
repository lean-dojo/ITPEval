(*
  Statement-only formalization of Logipedia corpus artifact nat.S_pred,
  catalog title nat.S_pred: every positive natural number is the successor of
  its predecessor. This file contains no proof.
*)

theory S_pred
  imports Main
begin

theorem S_pred:
  "\<forall>n :: nat. 0 < n \<longrightarrow> Suc (Nat.pred n) = n"
  sorry

end
