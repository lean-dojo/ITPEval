(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_b3:
  every finite carrier with at least two elements admits a right-cancellative
  binary operation that is nonassociative on every triple. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1984_b3 =
  ``let putnam_1984_b3_solution = T
    in
      (((FINITE (UNIV : 'a set) /\
         2 <= CARD (UNIV : 'a set))
        ==>
        ?mul : 'a -> 'a -> 'a.
          !x y z : 'a.
            (mul x z = mul y z ==> x = y) /\
            mul x (mul y z) <> mul (mul x y) z)
       <=>
       putnam_1984_b3_solution)``;
