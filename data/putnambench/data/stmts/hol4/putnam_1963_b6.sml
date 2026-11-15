(*
  Statement-only formalization of PutnamBench artifact putnam_1963_b6:
  stabilization after two iterations of taking every closed segment between
  pairs of points in a nonempty Euclidean set of dimension one, two, or three.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory;

val putnam_1963_b6 =
  ``let closed_segment =
      \p q : 'a -> real.
      \x : 'a -> real.
        ?t : real.
          0 <= t /\ t <= 1 /\
          x = (\i : 'a. (1 - t) * p i + t * q i)
    in
    let S =
      \B : ('a -> real) set.
      \x : 'a -> real.
        ?p q : 'a -> real.
          p IN B /\ q IN B /\ closed_segment p q x
    in
      !A : num -> ('a -> real) set.
        FINITE (UNIV : 'a set) /\
        1 <= CARD (UNIV : 'a set) /\
        CARD (UNIV : 'a set) <= 3 /\
        (?p : 'a -> real. p IN A 0) /\
        (!n : num. 1 <= n ==> A n = S (A (n - 1)))
        ==>
        !n : num. 2 <= n ==> A n = A (n + 1)``;
