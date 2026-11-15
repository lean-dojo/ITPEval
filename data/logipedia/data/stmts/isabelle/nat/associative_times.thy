(*
  Statement-only formalization of Logipedia corpus artifact
  nat.associative_times, catalog title nat.associative_times: multiplication
  on natural numbers is associative. This file contains no proof.
*)

theory associative_times
  imports Main
begin

theorem associative_times:
  "\<forall>x y z :: nat. (x * y) * z = x * (y * z)"
  sorry

end
