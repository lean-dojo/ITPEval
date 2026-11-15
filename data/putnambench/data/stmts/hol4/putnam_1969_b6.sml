(*
  Statement-only formalization of PutnamBench artifact putnam_1969_b6:
  rectangular real matrices whose product is the specified 3 by 3 matrix
  have reverse product equal to nine times the 2 by 2 identity matrix. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_1969_b6 =
  ``!A : num -> num -> real.
    !B : num -> num -> real.
    !p : num -> num -> real.
      p 0 0 = 8 /\ p 0 1 = 2 /\ p 0 2 = ~2 /\
      p 1 0 = 2 /\ p 1 1 = 5 /\ p 1 2 = 4 /\
      p 2 0 = ~2 /\ p 2 1 = 4 /\ p 2 2 = 5 /\
      (!i j : num.
         i < 3 /\ j < 3
         ==>
         SIGMA (\k : num. A i k * B k j) (count 2) = p i j)
      ==>
      (!i j : num.
         i < 2 /\ j < 2
         ==>
         SIGMA (\k : num. B i k * A k j) (count 3) =
           if i = j then 9 else 0)``;
