(*
  Statement-only formalization of Logipedia corpus artifact nat.times_n_1,
  catalog title "nat.times_n_1": every natural number equals itself multiplied
  by one, represented as the successor of zero. This file contains no proof.
*)

theory times_n_1
  imports Main
begin

theorem times_n_1:
  "\<forall>n :: nat. n = n * Suc 0"
  sorry

end
