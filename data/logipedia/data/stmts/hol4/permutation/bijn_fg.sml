(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.bijn_fg (catalog title "permutation.bijn_fg"): functions
  surjective on the natural-number interval from zero through n remain
  surjective there under composition. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_permutation_bijn_def = new_definition (
  "logipedia_permutation_bijn_def",
  ``logipedia_permutation_bijn (f : num -> num) (n : num) <=>
      !m : num.
        m <= n ==>
        ?p : num. p <= n /\ f p = m``);

val permutation_bijn_fg =
  ``!(f : num -> num) (g : num -> num) (n : num).
      logipedia_permutation_bijn f n ==>
      logipedia_permutation_bijn g n ==>
      logipedia_permutation_bijn (\p. f (g p)) n``;
