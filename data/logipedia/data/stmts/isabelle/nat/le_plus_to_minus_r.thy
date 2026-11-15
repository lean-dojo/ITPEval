(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_plus_to_minus_r, catalog title "nat.le_plus_to_minus_r": if the sum
  of two natural numbers a and b is at most c, then a is at most c minus b,
  using truncated natural subtraction. This file contains no proof.
*)

theory le_plus_to_minus_r
  imports Main
begin

theorem le_plus_to_minus_r:
  "\<forall>a b c :: nat. a + b \<le> c \<longrightarrow> a \<le> c - b"
  sorry

end
