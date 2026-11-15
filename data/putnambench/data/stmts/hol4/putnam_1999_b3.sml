(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_b3:
  the two-variable limit at (1,1), within the half-open unit square, of a
  normalized double power series over positive integer pairs whose ratio lies
  between 1/2 and 2 is 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory seqTheory
     transcTheory;

val putnam_1999_b3 =
  ``let A =
      {xy : real # real |
         0 <= FST xy /\ FST xy < 1 /\
         0 <= SND xy /\ SND xy < 1}
    in
    let S =
      \(x : real) (y : real).
        suminf
          (\m : num.
             suminf
               (\n : num.
                  if 0 < m /\ 0 < n /\
                     1 / 2 <= (&m : real) / &n /\
                     (&m : real) / &n <= 2
                  then x pow m * y pow n
                  else 0))
    in
    let dist =
      \xy : real # real.
        sqrt
          ((FST xy - 1) pow 2 +
           (SND xy - 1) pow 2)
    in
      !e : real.
        0 < e
        ==>
        ?d : real.
          0 < d /\
          !xy : real # real.
            xy IN A /\
            0 < dist xy /\
            dist xy < d
            ==>
            abs
              ((1 - FST xy * SND xy pow 2) *
               (1 - FST xy pow 2 * SND xy) *
               S (FST xy) (SND xy) -
               3) < e``;
