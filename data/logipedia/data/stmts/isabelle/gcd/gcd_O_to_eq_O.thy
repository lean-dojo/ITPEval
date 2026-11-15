(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.gcd_O_to_eq_O, catalog title "gcd.gcd_O_to_eq_O": if the greatest
  common divisor of two natural numbers is zero, then both numbers are zero.
  This file contains no proof.
*)

theory gcd_O_to_eq_O
  imports Main
begin

theorem gcd_O_to_eq_O:
  "\<forall>m n :: nat. gcd m n = 0 \<longrightarrow> m = 0 \<and> n = 0"
  sorry

end
