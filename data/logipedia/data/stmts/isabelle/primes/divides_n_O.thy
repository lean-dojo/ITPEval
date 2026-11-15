(*
  Statement-only formalization of Logipedia corpus artifact
  primes.divides_n_O, catalog title primes.divides_n_O: every natural number
  divides zero. This file contains no proof.
*)

theory divides_n_O
  imports Main
begin

theorem divides_n_O:
  "\<forall>n :: nat. n dvd 0"
  sorry

end
