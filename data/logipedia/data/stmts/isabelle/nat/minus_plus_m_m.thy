(*
  Statement-only formalization of Logipedia corpus artifact
  nat.minus_plus_m_m, catalog title nat.minus_plus_m_m: subtracting a natural
  number from its sum with another natural number recovers the other number.
  This file contains no proof.
*)

theory minus_plus_m_m
  imports Main
begin

theorem minus_plus_m_m:
  "\<forall>n m :: nat. n = (n + m) - m"
  sorry

end
