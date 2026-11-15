(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_a1:
  existence of three real polynomials whose combination of absolute values
  equals the specified piecewise-linear function on every real input. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory polyTheory;

val putnam_1999_a1 =
  ``let putnam_1999_a1_solution = T
    in
      ((?f g h : real list.
          !x : real.
            abs (poly f x) - abs (poly g x) + poly h x =
              if x < ~1 then ~1
              else if x <= 0 then 3 * x + 2
              else ~2 * x + 2)
       <=>
       putnam_1999_a1_solution)``;
