(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_plus_l, catalog title "nat.monotonic_le_plus_l": adding a
  fixed natural number on the right preserves the natural-number order. This
  file contains no proof.
*)

theory monotonic_le_plus_l
  imports Main
begin

theorem logipedia_nat_monotonic_le_plus_l:
  "\<forall>m x y :: nat. x \<le> y \<longrightarrow> x + m \<le> y + m"
  sorry

end
