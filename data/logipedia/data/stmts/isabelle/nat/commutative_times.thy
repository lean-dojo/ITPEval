(*
  Statement-only formalization of Logipedia corpus artifact
  nat.commutative_times, catalog title nat.commutative_times: multiplication
  on natural numbers is commutative. This file contains no proof.
*)

theory commutative_times
  imports Main
begin

theorem commutative_times:
  "\<forall>x y :: nat. x * y = y * x"
  sorry

end
