(*
  Statement-only formalization of Logipedia corpus artifact
  nat.minus_minus_comm, catalog title nat.minus_minus_comm: iterated truncated
  subtraction on natural numbers is unchanged when the two subtrahends are
  exchanged. This file contains no proof.
*)

theory minus_minus_comm
  imports Main
begin

theorem logipedia_nat_minus_minus_comm:
  "\<forall>a b c :: nat. (a - b) - c = (a - c) - b"
  sorry

end
