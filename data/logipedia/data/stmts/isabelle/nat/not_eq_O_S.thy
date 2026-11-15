(*
  Statement-only formalization of Logipedia corpus artifact nat.not_eq_O_S,
  catalog title "nat.not_eq_O_S": zero is unequal to the successor of every
  natural number. This file contains no proof.
*)

theory not_eq_O_S
  imports Main
begin

theorem logipedia_nat_not_eq_O_S:
  "\<forall>n :: nat. 0 \<noteq> Suc n"
  sorry

end
