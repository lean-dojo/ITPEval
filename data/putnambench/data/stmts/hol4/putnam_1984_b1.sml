(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_b1:
  the factorial-sum sequence satisfies the stated recurrence for the integer
  polynomials x + 3 and -x - 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pred_setTheory;

val putnam_1984_b1 =
  ``let eval_int_poly =
      \coeffs x.
        FOLDR (\a acc. a + x * acc) (0 : int) coeffs
    in
    let P = ([3; 1] : int list)
    in
    let Q = ([~2; ~1] : int list)
    in
      !f : num -> int.
        (!n : num.
           0 < n
           ==>
           f n =
             ITSET
               (\i acc. int_of_num (FACT i) + acc)
               (count (n + 1) DIFF count 1)
               (0 : int))
        ==>
        !n : num.
          1 <= n
          ==>
          f (n + 2) =
            eval_int_poly P (int_of_num n) * f (n + 1) +
            eval_int_poly Q (int_of_num n) * f n``;
