(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_gcd_l, catalog title "gcd.divides_gcd_l": the greatest common
  divisor of two natural numbers divides the first number. This file contains
  no proof.
*)

theory divides_gcd_l
  imports Main
begin

theorem divides_gcd_l:
  "\<forall>n m :: nat. gcd n m dvd n"
  sorry

end
