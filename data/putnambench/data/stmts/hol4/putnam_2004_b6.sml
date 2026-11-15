(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_b6:
  a nonempty set of positive integers whose positive difference set has an
  increasing enumeration with unbounded consecutive gaps has asymptotic
  density zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_topologyTheory;

val putnam_2004_b6 =
  ``!A B : num set. !N : real -> num. !b : num -> num.
      (?a : num. a IN A) /\
      (!a : num. a IN A ==> 0 < a) /\
      (!x : real.
         N x = CARD {a : num | a IN A /\ (&a : real) <= x}) /\
      B =
        {d : num |
           0 < d /\
           ?a a' : num.
             a IN A /\ a' IN A /\ d = a - a'} /\
      IMAGE b UNIV = B /\
      (!i : num. b i < b (i + 1)) /\
      (!r : num. ?i : num. r <= b (i + 1) - b i)
      ==>
      ((\x : real. &(N x) / x) --> 0) at_posinfinity``;
