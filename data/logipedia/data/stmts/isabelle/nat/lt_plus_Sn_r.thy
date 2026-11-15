(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_plus_Sn_r,
  catalog title "nat.lt_plus_Sn_r": every natural number is strictly less than
  itself plus another natural number and a successor. This file contains no proof.
*)

theory lt_plus_Sn_r
  imports Main
begin

theorem logipedia_nat_lt_plus_Sn_r:
  "\<forall>a x n :: nat. a < (a + x) + Suc n"
  sorry

end
