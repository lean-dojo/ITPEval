(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_minus_l, catalog title nat.monotonic_le_minus_l: truncated
  subtraction on natural numbers is monotone in its left operand. This file
  contains no proof.
*)

theory monotonic_le_minus_l
  imports Main
begin

theorem logipedia_nat_monotonic_le_minus_l:
  "\<forall>p q n :: nat. q \<le> p \<longrightarrow> q - n \<le> p - n"
  sorry

end
