(*
  Statement-only formalization of Logipedia corpus artifact
  nat.distributive_times_plus_r, catalog title nat.distributive_times_plus_r:
  natural-number multiplication distributes over addition on the right.
  This file contains no proof.
*)

theory distributive_times_plus_r
  imports Main
begin

theorem distributive_times_plus_r:
  "\<forall>a b c :: nat. (b + c) * a = b * a + c * a"
  sorry

end
