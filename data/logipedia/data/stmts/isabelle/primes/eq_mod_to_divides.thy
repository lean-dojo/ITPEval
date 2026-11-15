(*
  Statement-only formalization of Logipedia corpus artifact
  primes.eq_mod_to_divides, catalog title "primes.eq_mod_to_divides":
  natural numbers with equal remainders modulo a positive natural modulus
  have a truncated difference divisible by that modulus. This file contains
  no proof.
*)

theory eq_mod_to_divides
  imports Main
begin

theorem eq_mod_to_divides:
  fixes n m q :: nat
  assumes "0 < q"
    and "n mod q = m mod q"
  shows "q dvd (n - m)"
  sorry

end
