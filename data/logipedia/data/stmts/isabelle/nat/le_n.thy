(*
  Statement-only formalization of Logipedia corpus artifact nat.le_n,
  catalog title "nat.le_n": every natural number is less than or equal to
  itself. This file contains no proof.
*)

theory le_n
  imports Main
begin

theorem logipedia_nat_le_n:
  "\<forall>n :: nat. n \<le> n"
  sorry

end
