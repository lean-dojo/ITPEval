(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_n_O,
  catalog title nat.minus_n_O: subtracting zero from any natural number
  yields that number. This file contains no proof.
*)

theory minus_n_O
  imports Main
begin

theorem minus_n_O:
  "\<forall>n :: nat. n = n - 0"
  sorry

end
