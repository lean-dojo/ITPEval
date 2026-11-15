(*
  Statement-only formalization of Logipedia corpus artifact nat.times_n_O,
  catalog title "nat.times_n_O": for every natural number, zero equals that
  number multiplied by zero. This file contains no proof.
*)

theory times_n_O
  imports Main
begin

theorem times_n_O:
  "\<forall>n :: nat. 0 = n * 0"
  sorry

end
