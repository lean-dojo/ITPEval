(*
  Statement-only formalization of Logipedia corpus artifact nat.plus_O_n,
  catalog title "nat.plus_O_n": zero added on the left leaves every natural
  number unchanged. This file contains no proof.
*)

theory plus_O_n
  imports Main
begin

theorem plus_O_n:
  "\<forall>n :: nat. n = 0 + n"
  sorry

end
