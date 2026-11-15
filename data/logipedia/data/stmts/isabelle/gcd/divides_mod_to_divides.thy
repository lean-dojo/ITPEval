(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_mod_to_divides, catalog title "gcd.divides_mod_to_divides":
  for natural numbers p, m, and positive n, if p divides the remainder of m
  modulo n and p divides n, then p divides m. This file contains no proof.
*)

theory divides_mod_to_divides
  imports Main
begin

theorem divides_mod_to_divides:
  fixes p m n :: nat
  assumes "0 < n"
    and "p dvd (m mod n)"
    and "p dvd n"
  shows "p dvd m"
  sorry

end
