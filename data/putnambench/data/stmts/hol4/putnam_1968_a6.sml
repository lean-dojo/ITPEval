(*
  Statement-only formalization of PutnamBench artifact putnam_1968_a6:
  the classification of nonconstant polynomials with coefficients in
  {1, -1} whose complex roots are all real. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory complexTheory;

val putnam_1968_a6 =
  ``!n : num. !a : num -> complex.
      1 <= n /\
      (!k : num. k <= n ==> (a k = 1 \/ a k = -1)) /\
      (!k : num. n < k ==> a k = 0)
      ==>
      ((!z : complex.
          ITSET
            (\k acc. a k * z pow k + acc)
            (count (n + 1))
            0 = 0
          ==>
          IM z = 0)
       <=>
       n = 1 \/
       (n = 2 /\
        a 0 = -a 2 /\
        (a 1 = a 2 \/ a 1 = -a 2)) \/
       (n = 3 /\
        ((a 0 = -a 3 /\ a 1 = -a 3 /\ a 2 = a 3) \/
         (a 0 = a 3 /\ a 1 = -a 3 /\ a 2 = -a 3))))``;
