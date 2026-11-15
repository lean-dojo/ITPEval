(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_le,
  catalog title "nat.minus_le": subtracting any natural number from another
  yields a result at most the original minuend. This file contains no proof.
*)

theory minus_le
  imports Main
begin

theorem logipedia_nat_minus_le:
  "\<forall>x y :: nat. x - y \<le> x"
  sorry

end
