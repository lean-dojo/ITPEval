(*
  Statement-only formalization of Logipedia corpus artifact nat.pred_Sn,
  catalog title "nat.pred_Sn": the predecessor of the successor of every
  natural number is that number. This file contains no proof.
*)

theory pred_Sn
  imports Main
begin

theorem pred_Sn:
  "\<forall>n :: nat. n = Nat.pred (Suc n)"
  sorry

end
