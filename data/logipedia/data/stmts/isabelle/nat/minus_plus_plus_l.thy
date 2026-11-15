(*
  Statement-only formalization of Logipedia corpus artifact
  nat.minus_plus_plus_l, catalog title nat.minus_plus_plus_l: adding the same
  natural number to both operands leaves their truncated difference unchanged.
  This file contains no proof.
*)

theory minus_plus_plus_l
  imports Main
begin

theorem minus_plus_plus_l:
  "\<forall>x y h :: nat. (x + h) - (y + h) = x - y"
  sorry

end
