(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_b3:
  continuity and nonvanishing of a real function at zero, together with
  differentiability there of a product and quotient, imply differentiability
  of the other factor. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory;

val putnam_2011_b3 =
  ``let putnam_2011_b3_solution = T
    in
      ((!f g : real -> real.
          g 0 <> 0 /\
          g contl 0 /\
          (\x : real. f x * g x) differentiable 0 /\
          (\x : real. f x / g x) differentiable 0
          ==>
          f differentiable 0)
       <=>
       putnam_2011_b3_solution)``;
