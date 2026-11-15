(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_b5:
  the specified odd-order real skew-symmetric matrix has rank twice its
  positive integer parameter. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory rich_listTheory sortingTheory;
open pred_setTheory realTheory real_sigmaTheory;

val putnam_1988_b5 =
  ``let valid_indices =
      \bound k : num.
      \xs : num list.
        LENGTH xs = k /\
        ALL_DISTINCT xs /\
        EVERY (\i : num. i < bound) xs
    in
    let minor_det =
      \A : num -> num -> real.
      \rows cols : num list.
        let k = LENGTH rows
        in
          SIGMA
            (\p : num list.
               (-1 : real) pow
                 CARD
                   {ij : num # num |
                      FST ij < SND ij /\
                      SND ij < k /\
                      EL (SND ij) p < EL (FST ij) p} *
               REAL_PROD_IMAGE
                 (\i : num.
                    A (EL i rows) (EL (EL i p) cols))
                 (count k))
            {p : num list | PERM p (GENLIST I k)}
    in
    let has_nonzero_minor =
      \bound : num.
      \A : num -> num -> real.
      \k : num.
        ?rows cols : num list.
          valid_indices bound k rows /\
          valid_indices bound k cols /\
          minor_det A rows cols <> 0
    in
    let has_rank =
      \bound : num.
      \A : num -> num -> real.
      \k : num.
        has_nonzero_minor bound A k /\
        (!l : num.
           k < l
           ==>
           ~has_nonzero_minor bound A l)
    in
      !n : num. !Mn : num -> num -> real.
        0 < n /\
        (!i j : num.
           i < 2 * n + 1 /\ j < 2 * n + 1
           ==>
           Mn i j = -(Mn j i)) /\
        (!i j : num.
           i < 2 * n + 1 /\ j < 2 * n + 1 /\
           j < i /\ i <= j + n
           ==>
           Mn i j = 1) /\
        (!i j : num.
           i < 2 * n + 1 /\ j < 2 * n + 1 /\
           j + n < i
           ==>
           Mn i j = -1)
        ==>
        has_rank (2 * n + 1) Mn (2 * n)``;
