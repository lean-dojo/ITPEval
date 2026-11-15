(*
  Statement-only formalization of Logipedia corpus artifact
  nat.commutative_plus, catalog title nat.commutative_plus: addition on
  natural numbers is commutative. This file contains no proof.
*)

theory commutative_plus
  imports Main
begin

theorem commutative_plus:
  "\<forall>x y :: nat. x + y = y + x"
  sorry

end
