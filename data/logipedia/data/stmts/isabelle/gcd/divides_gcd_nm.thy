(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_gcd_nm, catalog title "gcd.divides_gcd_nm": the greatest common
  divisor of any two natural numbers divides both the second number and the
  first number. This file contains no proof.
*)

theory divides_gcd_nm
  imports Main
begin

theorem divides_gcd_nm:
  "\<forall>n m :: nat. gcd n m dvd m \<and> gcd n m dvd n"
  sorry

end
