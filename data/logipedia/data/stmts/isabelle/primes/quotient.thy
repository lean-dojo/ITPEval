(*
  Statement-only formalization of Logipedia corpus artifact primes.quotient,
  catalog title "primes.quotient": a natural number divides any natural
  multiple formed by multiplying it by a natural quotient. This file contains
  no proof.
*)

theory quotient
  imports Main
begin

theorem quotient:
  fixes n m q :: nat
  assumes "m = n * q"
  shows "n dvd m"
  sorry

end
