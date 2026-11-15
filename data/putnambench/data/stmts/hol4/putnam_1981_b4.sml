(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1981_b4:
  the falsity of the assertion that a real 5 by 7 matrix subspace containing
  ranks 0, 1, 2, 4, and 5 must also contain rank 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory rich_listTheory sortingTheory;
open pred_setTheory fcpTheory realTheory real_sigmaTheory matrixTheory;

val putnam_1981_b4 =
  ``let valid_indices =
      \bound k : num.
      \xs : num list.
        LENGTH xs = k /\
        ALL_DISTINCT xs /\
        EVERY (\i : num. i < bound) xs
    in
    let minor_det =
      \A : real['N]['M].
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
                    A ' (EL i rows) ' (EL (EL i p) cols))
                 (count k))
            {p : num list | PERM p (GENLIST I k)}
    in
    let has_nonzero_minor =
      \A : real['N]['M].
      \k : num.
        ?rows cols : num list.
          valid_indices 5 k rows /\
          valid_indices 7 k cols /\
          minor_det A rows cols <> 0
    in
    let has_rank =
      \A : real['N]['M].
      \k : num.
        has_nonzero_minor A k /\
        ~has_nonzero_minor A (SUC k)
    in
    let VAB =
      \V : real['N]['M] set.
        !A B : real['N]['M].
        !r s : real.
          A IN V /\ B IN V ==> r * A + s * B IN V
    in
      dimindex (:'M) = 5 /\
      dimindex (:'N) = 7
      ==>
      ((!V : real['N]['M] set.
          VAB V /\
          (?A : real['N]['M]. A IN V /\ has_rank A 0) /\
          (?A : real['N]['M]. A IN V /\ has_rank A 1) /\
          (?A : real['N]['M]. A IN V /\ has_rank A 2) /\
          (?A : real['N]['M]. A IN V /\ has_rank A 4) /\
          (?A : real['N]['M]. A IN V /\ has_rank A 5)
          ==>
          ?A : real['N]['M]. A IN V /\ has_rank A 3)
       <=>
       F)``;
