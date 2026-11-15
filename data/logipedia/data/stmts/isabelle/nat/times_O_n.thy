(*
  Statement-only formalization of Logipedia corpus artifact nat.times_O_n,
  catalog title "nat.times_O_n": zero multiplied on the left by any natural
  number is zero. This file contains no proof.
*)

theory times_O_n
  imports Main
begin

theorem times_O_n:
  "\<forall>n :: nat. 0 = 0 * n"
  sorry

end
