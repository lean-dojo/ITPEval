(*
  Statement-only formalization of Logipedia corpus artifact
  cong.let_clause_73, catalog title cong.let_clause_73: for natural numbers,
  under a positive-modulus assumption, exchanging the first two summands of
  a right-associated three-term sum preserves equality. This file contains
  no proof.
*)

theory let_clause_73
  imports Main
begin

theorem let_clause_73:
  fixes n m p x134 x135 x136 :: nat
  assumes "0 < p"
  shows "x134 + (x135 + x136) = x135 + (x134 + x136)"
  sorry

end
