(*
  Statement-only formalization of Logipedia corpus artifact
  nat.distributive_times_plus, catalog title nat.distributive_times_plus:
  natural-number multiplication distributes over addition on the left.
  This file contains no proof.
*)

theory distributive_times_plus
  imports Main
begin

theorem distributive_times_plus:
  "\<forall>x y z :: nat. x * (y + z) = x * y + x * z"
  sorry

end
