(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_b6:
  the limit of a normalized power of a positive real sequence defined by a
  reciprocal k-th-root recurrence. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory real_topologyTheory transcTheory;

val putnam_2006_b6 =
  ``!k : num. !a : num -> real.
      1 < k /\
      0 < a 0 /\
      (!n : num.
         a (n + 1) =
           a n + 1 / (a n powr (1 / (&k : real))))
      ==>
      (((\n : num.
           a n pow (k + 1) / ((&n : real) pow k)) -->
        (((&(k + 1) : real) / (&k : real)) pow k))
       sequentially)``;
