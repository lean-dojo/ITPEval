(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_b4:
  no real 2 by 2 matrix has matrix sine, defined by its usual power series,
  equal to the matrix [[1, 1996], [0, 1]]. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory fcpTheory realTheory real_sigmaTheory seqTheory;
open matrixTheory;

val putnam_1996_b4 =
  ``let matrix_pow =
      \A : real['N]['N].
        \n : num.
          FUNPOW
            (\B : real['N]['N]. matrix$matrix_mul A B)
            n
            (matrix$mat 1)
    in
    let matsin =
      \A : real['N]['N].
        ((FCP i j.
            suminf
              (\n : num.
                 ((~1 : real) pow n / &(FACT (2 * n + 1))) *
                 (matrix_pow A (2 * n + 1)) ' i ' j)) :
          real['N]['N])
    in
    let mat1996 =
      ((FCP i j.
          if i = 0 /\ j = 0 then 1
          else if i = 0 /\ j = 1 then 1996
          else if i = 1 /\ j = 0 then 0
          else if i = 1 /\ j = 1 then 1
          else 0) :
        real['N]['N])
    in
    let putnam_1996_b4_solution = F
    in
      dimindex (:'N) = 2
      ==>
      ((?A : real['N]['N]. matsin A = mat1996) <=>
       putnam_1996_b4_solution)``;
