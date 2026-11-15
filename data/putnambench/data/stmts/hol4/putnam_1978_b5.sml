(*
  Statement-only formalization of PutnamBench artifact putnam_1978_b5:
  the degree-four real polynomial 4*x^4 - 4*x^2 + 1 maps [-1,1] into
  [0,1] and has maximal fourth coefficient among all such polynomials.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open listTheory realTheory polyTheory;

val putnam_1978_b5 =
  ``let solution = ([1; 0; ~4; 0; 4] : real list) in
    let admissible =
      \p : real list.
        degree p = 4 /\
        !x : real.
          ~1 <= x /\ x <= 1
          ==>
          0 <= poly p x /\ poly p x <= 1
    in
      admissible solution /\
      !p : real list.
        admissible p
        ==>
        EL 4 (normalize p) <= EL 4 (normalize solution)``;
