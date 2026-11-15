(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_a2:
  sqrt 2 is the limit of a real sequence whose terms are differences of cube
  roots of nonnegative integers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory real_topologyTheory transcTheory;

val putnam_1990_a2 =
  ``((?s : num -> real.
        (!i : num.
           ?n : num.
             ?m : num.
               s i =
                 (&n : real) powr ((1 : real) / 3) -
                 (&m : real) powr ((1 : real) / 3)) /\
        (s --> sqrt 2) sequentially) <=>
     T)``;
