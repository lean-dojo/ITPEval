(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_O_S,
  catalog title "nat.lt_O_S": zero is strictly less than the successor of
  every natural number. This file contains no proof.
*)

theory lt_O_S
  imports Main
begin

theorem logipedia_nat_lt_O_S:
  "\<forall>n :: nat. 0 < Suc n"
  sorry

end
