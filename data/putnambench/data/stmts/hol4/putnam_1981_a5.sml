(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1981_a5:
  the claimed lower bound on the number of distinct real roots of a polynomial
  built from a real polynomial and its derivative. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory polyTheory;

val putnam_1981_a5 =
  ``let Q =
      \P : real list.
        poly_add
          (poly_mul
             (poly_mul ([1; 0; 1] : real list) P)
             (diff P))
          (poly_mul
             ([0; 1] : real list)
             (poly_add
                (P poly_exp 2)
                ((diff P) poly_exp 2)))
    in
      let n =
        \P : real list.
          if FINITE {x : real | x > 1 /\ poly P x = 0}
          then &(CARD {x : real | x > 1 /\ poly P x = 0})
          else 0
      in
        ((!P : real list.
            (if FINITE {x : real | poly (Q P) x = 0}
             then &(CARD {x : real | poly (Q P) x = 0})
             else 0) >=
            2 * n P - 1)
         <=> T)``;
