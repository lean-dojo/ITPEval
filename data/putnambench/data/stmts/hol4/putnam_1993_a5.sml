(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_a5:
  the sum of three definite integrals of the specified squared rational
  function is a rational number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory realTheory intrealTheory integrationTheory;

val putnam_1993_a5 =
  ``let f =
      \x : real.
        ((x pow 2 - x) / (x pow 3 - 3 * x + 1)) pow 2
    in
      ?p q : int.
        q <> 0 /\
        integration$integral (interval [~100, ~10]) f +
        integration$integral (interval [1 / 101, 1 / 11]) f +
        integration$integral (interval [101 / 100, 11 / 10]) f =
          real_of_int p / real_of_int q``;
