(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_plus_r, catalog title "nat.monotonic_le_plus_r": adding a
  fixed natural number on the left preserves the natural-number order. This
  file contains no proof.
*)

theory monotonic_le_plus_r
  imports Main
begin

theorem logipedia_nat_monotonic_le_plus_r:
  "\<forall>n x y :: nat. x \<le> y \<longrightarrow> n + x \<le> n + y"
  sorry

end
