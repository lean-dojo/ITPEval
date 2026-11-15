(*
  Statement-only formalization of Logipedia corpus artifact
  primes.divides_to_le, catalog title "primes.divides_to_le": a natural
  divisor of a positive natural number is at most that number. This file
  contains no proof.
*)

theory divides_to_le
  imports Main
begin

theorem divides_to_le:
  "\<forall>n m :: nat. 0 < m \<longrightarrow> n dvd m \<longrightarrow> n \<le> m"
  sorry

end
