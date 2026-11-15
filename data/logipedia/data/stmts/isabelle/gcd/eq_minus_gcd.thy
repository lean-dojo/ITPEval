(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.eq_minus_gcd, catalog title "gcd.eq_minus_gcd": for every pair of
  natural numbers, natural coefficients make one of the two truncated
  differences of multiples equal their greatest common divisor. This file
  contains no proof.
*)

theory eq_minus_gcd
  imports Main
begin

theorem eq_minus_gcd:
  "\<forall>m n :: nat. \<exists>a b :: nat.
    a * n - b * m = gcd n m \<or>
    b * m - a * n = gcd n m"
  sorry

end
