(*
  Statement-only formalization of Logipedia corpus artifact
  cong.let_clause_1034, catalog title cong.let_clause_1034: under an unused
  positive-natural assumption, every natural number is its remainder modulo
  any natural divisor plus that divisor times its quotient. This file contains
  no proof.
*)

theory let_clause_1034
  imports Main
begin

theorem let_clause_1034:
  fixes n m p x2515 x2516 :: nat
  assumes "0 < p"
  shows "x2515 = x2515 mod x2516 + x2516 * (x2515 div x2516)"
  sorry

end
