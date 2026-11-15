(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.bijn_transpose (catalog title "permutation.bijn_transpose"):
  swapping two bounded natural numbers is surjective on the initial segment
  containing them. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val permutation_bijn_transpose =
  ``!(n : num) (i : num) (j : num).
      i <= n ==>
      j <= n ==>
      !m : num.
        m <= n ==>
        ?p : num.
          p <= n /\
          (if p = i then j else if p = j then i else p) = m``;
