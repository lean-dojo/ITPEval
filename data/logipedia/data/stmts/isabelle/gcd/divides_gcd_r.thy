(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_gcd_r, catalog title "gcd.divides_gcd_r": the greatest common
  divisor of two natural numbers divides the second number. This file contains
  no proof.
*)

theory divides_gcd_r
  imports Main
begin

theorem divides_gcd_r:
  "\<forall>n m :: nat. gcd n m dvd m"
  sorry

end
