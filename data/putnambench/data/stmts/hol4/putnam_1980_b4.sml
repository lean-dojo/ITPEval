(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1980_b4:
  a finite set and 1,066 subsets each containing more than half its elements
  admit a 10-element hitting set. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1980_b4 =
  ``!X : 'a set. !A : num -> 'a set.
      FINITE X /\
      10 <= CARD X /\
      (!i : num.
         i IN count 1066
         ==>
         A i SUBSET X /\
         CARD (A i) > CARD X DIV 2)
      ==>
      ?Y : 'a set.
        Y SUBSET X /\
        CARD Y = 10 /\
        !i : num.
          i IN count 1066
          ==>
          ?y : 'a.
            y IN Y /\ y IN A i``;
