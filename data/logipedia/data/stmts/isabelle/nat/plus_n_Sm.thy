(*
  Statement-only formalization of Logipedia corpus artifact nat.plus_n_Sm,
  catalog title "nat.plus_n_Sm": the successor of a sum of natural numbers
  equals adding the successor of the second summand. This file contains no proof.
*)

theory plus_n_Sm
  imports Main
begin

theorem plus_n_Sm:
  "\<forall>n m :: nat. Suc (n + m) = n + Suc m"
  sorry

end
