(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_b4:
  the greatest common divisor of the entries of A^n minus the identity tends
  to infinity for the integer matrix A = [[3, 2], [4, 3]]. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory integerTheory fcpTheory;

val putnam_1994_b4 =
  ``let matrix_mul =
      \B C : int['N]['N].
        ((FCP i j.
            B ' i ' 0 * C ' 0 ' j + B ' i ' 1 * C ' 1 ' j) :
          int['N]['N])
    in
    let matrix_one =
      ((FCP i j. if i = j then 1 else 0) : int['N]['N])
    in
    let A =
      ((FCP i j.
          if i = 0 /\ j = 0 then 3
          else if i = 0 /\ j = 1 then 2
          else if i = 1 /\ j = 0 then 4
          else if i = 1 /\ j = 1 then 3
          else 0) : int['N]['N])
    in
    let matrix_pow =
      \n : num.
        FUNPOW
          (\B : int['N]['N]. matrix_mul B A)
          n matrix_one
    in
    let matrix_sub =
      \B C : int['N]['N].
        ((FCP i j. B ' i ' j - C ' i ' j) : int['N]['N])
    in
    let matrix_gcd =
      \B : int['N]['N].
        gcd
          (gcd
            (gcd
              (Num (ABS (B ' 0 ' 0)))
              (Num (ABS (B ' 0 ' 1))))
            (Num (ABS (B ' 1 ' 0))))
          (Num (ABS (B ' 1 ' 1)))
    in
    let d =
      \n : num. matrix_gcd (matrix_sub (matrix_pow n) matrix_one)
    in
      dimindex (:'N) = 2
      ==>
      !k : num.
        ?N : num.
          !n : num. N <= n ==> k <= d n``;
