(*
  Statement-only formalization of Logipedia corpus artifact gcd.gcd_O_l,
  catalog title "gcd.gcd_O_l": the greatest common divisor of zero and any
  natural number is that natural number. This file contains no proof.
*)

theory gcd_O_l
  imports Main
begin

theorem gcd_O_l:
  "\<forall>m :: nat. gcd 0 m = m"
  sorry

end
