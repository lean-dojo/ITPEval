(*
  Statement-only formalization of Logipedia corpus artifact nat.times_n_Sm,
  catalog title "nat.times_n_Sm": for all natural numbers n and m, adding n
  to n times m equals n times the successor of m. This file contains no proof.
*)

theory times_n_Sm
  imports Main
begin

theorem times_n_Sm:
  "\<forall>n m :: nat. n + n * m = n * Suc m"
  sorry

end
