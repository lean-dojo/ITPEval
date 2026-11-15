(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.eq_to_bijn (catalog title "permutation.eq_to_bijn"): bounded
  surjectivity on the natural-number interval from zero through n is preserved
  when two functions agree throughout that interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_permutation_bijn_def = new_definition (
  "logipedia_permutation_bijn_def",
  ``logipedia_permutation_bijn (f : num -> num) (n : num) <=>
      !m : num.
        m <= n ==>
        ?p : num. p <= n /\ f p = m``);

val permutation_eq_to_bijn =
  ``!(f : num -> num) (g : num -> num) (n : num).
      (!i : num. i <= n ==> f i = g i) ==>
      logipedia_permutation_bijn f n ==>
      logipedia_permutation_bijn g n``;
