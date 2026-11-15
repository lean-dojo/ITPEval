(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_b1:
  positive integers have a unique base-10 over-expansion exactly when their
  ordinary decimal expansion contains no zero digit. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory numposrepTheory pred_setTheory;

val putnam_2014_b1 =
  ``!(overexpansion : num -> num list -> bool) (S : num set).
      overexpansion =
        (\N d.
           d <> [] /\
           N =
             ITSET
               (\i acc. EL i d * 10 ** i + acc)
               (count (LENGTH d))
               0 /\
           LAST d <> 0 /\
           EVERY (\a : num. a <= 10) d) /\
      (!N : num.
         N IN S <=>
         0 < N /\ ?!d : num list. overexpansion N d)
      ==>
      S =
        {N : num |
           0 < N /\
           EVERY (\a : num. a <> 0) (n2l 10 N)}``;
