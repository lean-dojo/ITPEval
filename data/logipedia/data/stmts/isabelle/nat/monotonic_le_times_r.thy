(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_times_r, catalog title "nat.monotonic_le_times_r":
  multiplication by a fixed natural number on the left preserves the
  natural-number order. This file contains no proof.
*)

theory monotonic_le_times_r
  imports Main
begin

theorem logipedia_nat_monotonic_le_times_r:
  "\<forall>n x y :: nat. x \<le> y \<longrightarrow> n * x \<le> n * y"
  sorry

end
