(*
  Statement-only formalization of Logipedia corpus artifact
  nat.distributive_times_minus, catalog title nat.distributive_times_minus:
  left multiplication distributes over truncated subtraction on natural
  numbers. This file contains no proof.
*)

theory distributive_times_minus
  imports Main
begin

theorem distributive_times_minus:
  "\<forall>a b c :: nat. a * (b - c) = (a * b) - (a * c)"
  sorry

end
