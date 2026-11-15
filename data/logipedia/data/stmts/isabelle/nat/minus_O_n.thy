(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_O_n,
  catalog title "nat.minus_O_n": subtracting any natural number from zero
  yields zero. This file contains no proof.
*)

theory minus_O_n
  imports Main
begin

theorem minus_O_n:
  "\<forall>n :: nat. 0 = 0 - n"
  sorry

end
