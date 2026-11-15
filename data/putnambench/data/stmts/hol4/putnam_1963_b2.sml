(*
  Statement-only formalization of PutnamBench artifact putnam_1963_b2:
  the set of real numbers 2^m * 3^n with integer exponents is dense among
  the positive real numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory realTheory intrealTheory
     real_topologyTheory transcTheory;

val putnam_1963_b2 =
  ``{x : real | 0 < x} SUBSET
      closure
        {x : real |
           ?m n : int.
             x =
               (2 : real) powr real_of_int m *
               (3 : real) powr real_of_int n}``;
