(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_minus_r, catalog title nat.monotonic_le_minus_r: truncated
  subtraction on natural numbers is antitone in its right operand, so q <= p
  implies n - p <= n - q. This file contains no proof.
*)

theory monotonic_le_minus_r
  imports Main
begin

theorem logipedia_nat_monotonic_le_minus_r:
  "\<forall>p q n :: nat. q \<le> p \<longrightarrow> n - p \<le> n - q"
  sorry

end
