(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus_n_r,
  catalog title "nat.le_plus_n_r": every natural number is less than or equal
  to itself plus any natural number. This file contains no proof.
*)

theory le_plus_n_r
  imports Main
begin

theorem le_plus_n_r:
  "\<forall>n m :: nat. m \<le> m + n"
  sorry

end
