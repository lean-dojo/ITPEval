(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_b4:
  the number of real-polynomial pairs whose squares sum to X^(2n) + 1 and
  whose degrees are strictly decreasing is 2^(n+1). This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory;

val putnam_2007_b4 =
  ``let finite_poly =
      \P : num -> real. FINITE {k : num | P k <> 0}
    in
    let square_coeff =
      \P : num -> real.
        \k : num.
          SIGMA
            (\i : num. P i * P (k - i))
            (count (k + 1))
    in
    let poly_degree =
      \P : num -> real. MAX_SET {k : num | P k <> 0}
    in
      !n : num.
        0 < n
        ==>
        CARD
          {pq : (num -> real) # (num -> real) |
             finite_poly (FST pq) /\
             finite_poly (SND pq) /\
             (!k : num.
                square_coeff (FST pq) k +
                  square_coeff (SND pq) k =
                if k = 0 \/ k = 2 * n then 1 else 0) /\
             poly_degree (FST pq) > poly_degree (SND pq)} =
        2 EXP (n + 1)``;
