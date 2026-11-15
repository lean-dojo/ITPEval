(*
  Statement-only formalization of Logipedia corpus artifact
  cong.let_clause_73 (catalog title "cong.let_clause_73"): for universally
  quantified natural numbers n, m, and p with p positive, swapping the first
  two addends in a three-term natural-number sum preserves its value. The
  parameters n and m do not occur in the equality. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val cong_let_clause_73 =
  ``!(n : num) (m : num) (p : num).
      0 < p
      ==>
      !(x134 : num) (x135 : num) (x136 : num).
        x134 + (x135 + x136) =
        x135 + (x134 + x136)``;
