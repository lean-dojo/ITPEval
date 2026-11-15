(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_times_to_divides, catalog title "gcd.divides_times_to_divides":
  a prime natural number that divides a product divides at least one of its
  two natural-number factors. This file contains no proof.
*)

theory divides_times_to_divides
  imports Main
begin

theorem divides_times_to_divides:
  fixes p n m :: nat
  assumes "prime p"
    and "p dvd (n * m)"
  shows "p dvd n \<or> p dvd m"
  sorry

end
