(*
  Statement-only formalization of PutnamBench artifact putnam_1968_a3:
  a Gray-code ordering of all subsets of an arbitrary finite set, beginning
  with the empty set and changing one element at each step. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val putnam_1968_a3 =
  ``!A : 'a set.
      FINITE A
      ==>
      ?l : ('a set) list.
        EL 0 l = {} /\
        (!i : num.
           i < LENGTH l
           ==>
           EL i l SUBSET A) /\
        (!S : 'a set.
           S SUBSET A
           ==>
           ?!i : num. i < LENGTH l /\ EL i l = S) /\
        (!i : num.
           i + 1 < LENGTH l
           ==>
           ?a : 'a.
             (a NOTIN EL i l /\
              EL (i + 1) l = a INSERT EL i l) \/
             (a NOTIN EL (i + 1) l /\
              EL i l = a INSERT EL (i + 1) l))``;
