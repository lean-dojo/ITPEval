(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_lt_plus_r, catalog title "nat.monotonic_lt_plus_r": for every
  natural number n, adding n on the left is strictly monotone on natural
  numbers. This file contains no proof.
*)

theory monotonic_lt_plus_r
  imports Main
begin

theorem monotonic_lt_plus_r:
  "\<forall>n x y :: nat. x < y \<longrightarrow> n + x < n + y"
  sorry

end
