(*
  Statement-only formalization of Logipedia corpus artifact
  primes.divides_n_n, catalog title primes.divides_n_n: every natural number
  divides itself. This file contains no proof.
*)

theory divides_n_n
  imports Main
begin

theorem divides_n_n:
  "\<forall>n :: nat. n dvd n"
  sorry

end
