(*
  Statement-only formalization of Logipedia corpus artifact nat.plus_n_O,
  catalog title nat.plus_n_O: every natural number equals itself plus zero.
  This file contains no proof.
*)

theory plus_n_O
  imports Main
begin

theorem plus_n_O:
  "\<forall>n :: nat. n = n + 0"
  sorry

end
