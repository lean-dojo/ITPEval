(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_minus_S_pred,
  catalog title nat.eq_minus_S_pred: subtracting a successor from a natural
  number equals the predecessor of subtracting its predecessor. This file
  contains no proof.
*)

theory eq_minus_S_pred
  imports Main
begin

theorem eq_minus_S_pred:
  "\<forall>n m :: nat. n - Suc m = Nat.pred (n - m)"
  sorry

end
