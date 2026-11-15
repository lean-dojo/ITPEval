(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_lt_plus_l, catalog title "nat.monotonic_lt_plus_l": for every
  fixed natural number n, adding n on the right strictly preserves the order
  of natural numbers. This file contains no proof.
*)

theory monotonic_lt_plus_l
  imports Main
begin

theorem monotonic_lt_plus_l:
  "\<forall>n x y :: nat. x < y \<longrightarrow> x + n < y + n"
  sorry

end
