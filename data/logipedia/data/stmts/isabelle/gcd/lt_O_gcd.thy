(*
  Statement-only formalization of Logipedia corpus artifact gcd.lt_O_gcd,
  catalog title "gcd.lt_O_gcd": if a natural number n is positive, then the
  greatest common divisor of any natural number m and n is positive. This file
  contains no proof.
*)

theory lt_O_gcd
  imports Main
begin

theorem lt_O_gcd:
  "\<forall>m n :: nat. 0 < n \<longrightarrow> 0 < gcd m n"
  sorry

end
