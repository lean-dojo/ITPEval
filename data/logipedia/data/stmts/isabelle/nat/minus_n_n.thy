(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_n_n,
  catalog title "nat.minus_n_n": subtracting a natural number from itself
  yields zero. This file contains no proof.
*)

theory minus_n_n
  imports Main
begin

theorem minus_n_n:
  "\<forall>n :: nat. 0 = n - n"
  sorry

end
