(*
  Statement-only formalization of Logipedia corpus artifact
  cong.let_clause_1034 (catalog title "cong.let_clause_1034"): for universally
  quantified natural numbers n, m, and p with p positive, the totalized
  natural-number quotient-remainder identity holds for every natural dividend
  and divisor. The parameters n and m do not occur in the identity. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val cong_let_clause_1034 =
  ``!(n : num) (m : num) (p : num).
      0 < p
      ==>
      !(x2515 : num) (x2516 : num).
        x2515 =
        x2515 MOD x2516 + x2516 * (x2515 DIV x2516)``;
