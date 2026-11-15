(*
  Statement-only formalization of Logipedia corpus artifact
  nat.lt_plus_to_minus_r, catalog title "nat.lt_plus_to_minus_r": if the sum
  of two natural numbers a and b is strictly less than c, then a is strictly
  less than c minus b, using truncated natural subtraction. This file contains
  no proof.
*)

theory lt_plus_to_minus_r
  imports Main
begin

theorem lt_plus_to_minus_r:
  "\<forall>a b c :: nat. a + b < c \<longrightarrow> a < c - b"
  sorry

end
