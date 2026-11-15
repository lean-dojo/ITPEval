(*
  Statement-only formalization of PutnamBench artifact putnam_1972_b6:
  a polynomial with constant term one and strictly increasing positive
  integer exponents has no complex zero of modulus less than
  (sqrt 5 - 1) / 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory complexTheory;

val putnam_1972_b6 =
  ``!k : num. !n : num -> num. !zpoly : complex -> complex.
      1 <= k /\
      (!i : num. i < k ==> 0 < n i) /\
      (!i j : num.
         i < k /\ j < k /\ i < j ==> n i < n j) /\
      zpoly =
        (\z : complex.
           1 +
           ITSET
             (\i acc. z pow (n i) + acc)
             (count k)
             0)
      ==>
      !z : complex.
        modu z < (sqrt 5 - 1) / 2
        ==>
        zpoly z <> 0``;
