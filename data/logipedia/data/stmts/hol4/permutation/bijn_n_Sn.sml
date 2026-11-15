(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.bijn_n_Sn (catalog title "permutation.bijn_n_Sn"): bounded
  surjectivity of a natural-number function extends from the initial segment
  through n to the segment through n + 1 when the function fixes n + 1. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val permutation_bijn_n_Sn =
  ``!(f : num -> num) (n : num).
      (!m : num.
         m <= n ==>
         ?p : num. p <= n /\ f p = m) ==>
      f (SUC n) = SUC n ==>
      !m : num.
        m <= SUC n ==>
        ?p : num. p <= SUC n /\ f p = m``;
