(*
  Statement-only formalization of Logipedia corpus artifact
  primes.reflexive_divides, catalog title "primes.reflexive_divides":
  natural-number divisibility is reflexive, so every natural number divides
  itself. This file contains no proof.
*)

theory reflexive_divides
  imports Main
begin

theorem reflexive_divides:
  "\<forall>n :: nat. n dvd n"
  sorry

end
