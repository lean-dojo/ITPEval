(*
  Statement-only formalization of PutnamBench artifact putnam_1964_b2:
  a maximal pairwise-intersecting family of subsets of a nonempty finite set
  contains exactly half of all subsets. This file contains no proof.
*)

let statement =
  `!n:num. !P:(A->bool)->bool.
     0 < n /\
     (:A) HAS_SIZE n /\
     FINITE P /\
     (!s t:A->bool.
        s IN P /\ t IN P
        ==> ~(s INTER t = {})) /\
     ~(?s:A->bool.
         ~(s IN P) /\
         (!t:A->bool.
            t IN P
            ==> ~(s INTER t = {})))
     ==> CARD P = 2 EXP (n - 1)`;;
