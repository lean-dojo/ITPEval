(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_S_S,
  catalog title nat.minus_S_S: subtracting one successor natural from another
  cancels the successor on both operands. This file contains no proof.
*)

theory minus_S_S
  imports Main
begin

theorem minus_S_S:
  "\<forall>n m :: nat. Suc n - Suc m = n - m"
  sorry

end
