(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_a2:
  whether distinct positive-dimensional real square matrices satisfying the
  specified cubic identities can have an invertible sum of squares. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory fcpTheory realTheory real_sigmaTheory;
open matrixTheory;

val putnam_1991_a2 =
  ``let matrix_square =
      \A : real['N]['N]. matrix$matrix_mul A A
    in
    let matrix_cube =
      \A : real['N]['N]. matrix$matrix_mul (matrix_square A) A
    in
    let matrix_invertible =
      \A : real['N]['N].
        ?C : real['N]['N].
          matrix$matrix_mul A C = matrix$mat 1 /\
          matrix$matrix_mul C A = matrix$mat 1
    in
    let putnam_1991_a2_solution = F
    in
      !n : num.
        0 < n /\
        dimindex (:'N) = n
        ==>
        ((?A B : real['N]['N].
            A <> B /\
            matrix_cube A = matrix_cube B /\
            matrix$matrix_mul (matrix_square A) B =
              matrix$matrix_mul (matrix_square B) A /\
            matrix_invertible
              (matrix$matrix_add (matrix_square A) (matrix_square B)))
         <=>
         putnam_1991_a2_solution)``;
