(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_plus,
  catalog title nat.minus_plus: iterated truncated subtraction on natural
  numbers equals subtraction of the sum. This file contains no proof.
*)

theory minus_plus
  imports Main
begin

theorem minus_plus:
  "\<forall>n m p :: nat. (n - m) - p = n - (m + p)"
  sorry

end
