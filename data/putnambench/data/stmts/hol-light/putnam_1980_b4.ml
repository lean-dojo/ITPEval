(*
  Statement-only formalization of PutnamBench artifact putnam_1980_b4:
  a family of 1066 subsets, each containing more than half of a finite set,
  has a 10-element hitting set. This file contains no proof.
*)

let statement =
  `!X:A->bool. !a:num->A->bool.
     FINITE X /\
     10 <= CARD X /\
     (!i:num.
        i IN 1..1066
        ==> a i SUBSET X /\ CARD X < 2 * CARD (a i))
     ==> ?Y:A->bool.
           Y SUBSET X /\
           CARD Y = 10 /\
           (!i:num.
              i IN 1..1066
              ==> ?y:A. y IN Y /\ y IN a i)`;;
