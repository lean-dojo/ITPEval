(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_a4:
  balanced zero counts on equal-length arcs of a finite binary circle force
  an arc realizing integral average zero and one counts. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pairTheory pred_setTheory;

val putnam_2013_a4 =
  ``!n k : num.
      !circle : num -> num.
      !ws : num -> num # num.
      !Zsum Nsum : int.
      0 < n /\
      0 < k /\
      (!i : num. i < n ==> circle i < 2) /\
      (!j : num.
         j < k ==> FST (ws j) < n /\ SND (ws j) <= n)
      ==>
      let Z =
        \w : num # num.
          SIGMA
            (\l : num.
               if circle ((FST w + l) MOD n) = 0
               then (1 : int)
               else 0)
            (count (SND w))
      in
      let N =
        \w : num # num.
          SIGMA
            (\l : num.
               if circle ((FST w + l) MOD n) = 1
               then (1 : int)
               else 0)
            (count (SND w))
      in
        (!w w' : num # num.
           FST w < n /\ SND w <= n /\
           FST w' < n /\ SND w' <= n /\
           SND w = SND w'
           ==>
           ABS (Z w - Z w') <= 1) /\
        int_of_num k * Zsum =
          SIGMA (\j : num. Z (ws j)) (count k) /\
        int_of_num k * Nsum =
          SIGMA (\j : num. N (ws j)) (count k)
        ==>
        ?w : num # num.
          FST w < n /\ SND w <= n /\
          Z w = Zsum /\ N w = Nsum``;
