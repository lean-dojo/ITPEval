(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a2:
  the real polynomials p for which p(p(x)) - x is a polynomial multiple of
  (p(x) - x)^2 are exactly the affine polynomials with slope 1 or -1.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open listTheory realTheory polyTheory;

val putnam_2024_a2 =
  ``!p : real list.
      ((?q : real list.
          !x : real.
            poly p (poly p x) - x =
            (poly p x - x) pow 2 * poly q x)
       <=>
       (?a : real.
          (!x : real. poly p x = x + a) \/
          (!x : real. poly p x = -x + a)))``;
