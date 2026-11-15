(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1980_a5:
  finiteness of the real endpoints at which both signed integrals of a
  nonconstant real polynomial times sine and cosine vanish. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory integrationTheory polyTheory;

val putnam_1980_a5 =
  ``let integral_to =
      \x : real.
      \f : real -> real.
        if 0 <= x then
          integration$integral (interval [0, x]) f
        else
          ~(integration$integral (interval [x, 0]) f)
    in
      !P : real list.
        degree P > 0
        ==>
        FINITE
          {x : real |
             integral_to x (\t : real. poly P t * sin t) = 0 /\
             integral_to x (\t : real. poly P t * cos t) = 0}``;
