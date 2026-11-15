(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_pred, catalog title nat.monotonic_pred: the predecessor
  function is monotone with respect to the natural-number order. This file
  contains no proof.
*)

theory monotonic_pred
  imports Main
begin

theorem monotonic_pred:
  "\<forall>x y :: nat. x \<le> y \<longrightarrow> Nat.pred x \<le> Nat.pred y"
  sorry

end
