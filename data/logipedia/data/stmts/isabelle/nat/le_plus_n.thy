(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus_n,
  catalog title "nat.le_plus_n": every natural number m is at most n + m
  for every natural number n. This file contains no proof.
*)

theory le_plus_n
  imports Main
begin

theorem logipedia_nat_le_plus_n:
  "\<forall>n m :: nat. m \<le> n + m"
  sorry

end
