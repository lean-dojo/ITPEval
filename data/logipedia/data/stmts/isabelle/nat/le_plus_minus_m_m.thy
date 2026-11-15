(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_plus_minus_m_m, catalog title "nat.le_plus_minus_m_m": every natural
  number n is at most the sum of n minus m and m, using truncated natural
  subtraction. This file contains no proof.
*)

theory le_plus_minus_m_m
  imports Main
begin

theorem le_plus_minus_m_m:
  "\<forall>n m :: nat. n \<le> (n - m) + m"
  sorry

end
