(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.permut_to_bijn (catalog title "permutation.permut_to_bijn"):
  a natural-number function that maps the inclusive interval from zero
  through n into itself and is injective there is surjective onto that
  interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val permutation_permut_to_bijn =
  ``!(n : num) (f : num -> num).
      ((!i : num. i <= n ==> f i <= n) /\
       !i j : num.
         i <= n ==>
         j <= n ==>
         f i = f j ==>
         i = j) ==>
      !m : num.
        m <= n ==>
        ?p : num. p <= n /\ f p = m``;
