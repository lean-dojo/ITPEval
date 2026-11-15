(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_a6:
  classification, according to whether c is at most one quarter, of the
  continuous real functions satisfying f(x) = f(x^2 + c). This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory;

val putnam_1996_a6 =
  ``!c : real.
      0 < c
      ==>
      !f : real -> real.
        (f continuous_on UNIV /\
         (!x : real. f x = f (x pow 2 + c)))
        <=>
        if c <= 1 / 4 then
          ?d : real. !x : real. f x = d
        else
          f continuous_on interval [0, c] /\
          f 0 = f c /\
          (!x : real. 0 < x ==> f x = f (x pow 2 + c)) /\
          (!x : real. x < 0 ==> f x = f (~x))``;
