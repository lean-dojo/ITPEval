(*
  Statement-only formalization of PutnamBench artifact putnam_1975_a4:
  for an odd integer m greater than one and the associated primitive
  2m-th complex root of unity theta, the reciprocal of 1 - theta is the
  explicit integer-coefficient polynomial sum of its positive odd powers.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory complexTheory;

val putnam_1975_a4 =
  ``!m : num. !theta : complex.
      ODD m /\ 1 < m /\
      theta = exp (i * (2 * pi / &(2 * m)))
      ==>
      1 / (1 - theta) =
        SIGMA
          (\j : num. theta pow (2 * j + 1))
          (count ((m - 1) DIV 2))``;
