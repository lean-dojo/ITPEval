(*
  Statement-only formalization of Logipedia corpus artifact
  nat.associative_plus, catalog title nat.associative_plus: addition on
  natural numbers is associative. This file contains no proof.
*)

theory associative_plus
  imports Main
begin

theorem associative_plus:
  "\<forall>x y z :: nat. (x + y) + z = x + (y + z)"
  sorry

end
