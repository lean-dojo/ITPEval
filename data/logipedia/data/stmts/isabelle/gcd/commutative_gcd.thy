(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.commutative_gcd, catalog title "gcd.commutative_gcd": the greatest
  common divisor of any two natural numbers is unchanged when its arguments
  are exchanged. This file contains no proof.
*)

theory commutative_gcd
  imports Main
begin

theorem commutative_gcd:
  "\<forall>n m :: nat. gcd n m = gcd m n"
  sorry

end
