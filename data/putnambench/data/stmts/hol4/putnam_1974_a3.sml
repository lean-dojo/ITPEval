(*
  Statement-only formalization of PutnamBench artifact putnam_1974_a3:
  the sum-of-two-squares criterion classifies primes represented by
  x^2 + 16y^2 and by 4x^2 + 4xy + 5y^2 into the residue classes 1 and 5
  modulo 8, respectively. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory integerTheory pairTheory pred_setTheory;

val putnam_1974_a3 =
  ``let solution =
      ({p : num | prime p /\ p MOD 8 = 1},
       {p : num | prime p /\ p MOD 8 = 5})
    in
      (!p : num.
         prime p /\ 2 < p
         ==>
         ((?m n : int.
              int_of_num p = m ** 2 + n ** 2)
          <=>
          p MOD 4 = 1))
      ==>
      !p : num.
        ((prime p /\ 2 < p /\
          (?x y : int.
             int_of_num p = x ** 2 + 16 * y ** 2))
         <=>
         p IN FST solution) /\
        ((prime p /\ 2 < p /\
          (?x y : int.
             int_of_num p =
               4 * x ** 2 + 4 * x * y + 5 * y ** 2))
         <=>
         p IN SND solution)``;
