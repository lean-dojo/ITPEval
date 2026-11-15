(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_b1:
  the number of configurations reachable by diagonal legal moves from the
  initial coin configuration on an m-by-n grid is the stated binomial
  coefficient. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory listTheory pairTheory pred_setTheory;

val putnam_2023_b1 =
  ``!m n : num.
      0 < m /\ 0 < n
      ==>
      let initcoins =
        \i j : num. i < m - 1 /\ j < n - 1
      in
      let legalmove =
        \coins1 coins2 : num -> num -> bool.
          ?i j : num.
            i < m - 1 /\
            j < n - 1 /\
            coins1 i j /\
            ~coins1 (i + 1) j /\
            ~coins1 i (j + 1) /\
            ~coins1 (i + 1) (j + 1) /\
            ~coins2 i j /\
            ~coins2 (i + 1) j /\
            ~coins2 i (j + 1) /\
            coins2 (i + 1) (j + 1) /\
            (!i' j' : num.
               (i', j') <> (i, j) /\
               (i', j') <> (i + 1, j) /\
               (i', j') <> (i, j + 1) /\
               (i', j') <> (i + 1, j + 1)
               ==>
               coins1 i' j' = coins2 i' j')
      in
      let legalseq =
        \seq : (num -> num -> bool) list.
          seq <> [] /\
          EL 0 seq = initcoins /\
          (!i : num.
             SUC i < LENGTH seq
             ==>
             legalmove (EL i seq) (EL (SUC i) seq))
      in
        {config : num -> num -> bool |
           ?seq : (num -> num -> bool) list.
             legalseq seq /\ config = LAST seq}
        HAS_SIZE binomial (m + n - 2) (m - 1)``;
