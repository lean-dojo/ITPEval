(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_a1:
  the number of integer points in the coordinate square [0,2011] x [0,2011]
  that
  cannot be endpoints of growing axis-aligned spirals is 10053. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pairTheory pred_setTheory;

val putnam_2011_a1 =
  ``let is_spiral =
      \P : (int # int) list.
        3 <= LENGTH P /\
        EL 0 P = (0, 0) /\
        ?l : num -> num.
          (!i : num.
             i < LENGTH P - 1
             ==>
             0 < l i) /\
          (!i j : num.
             i < j /\ j < LENGTH P - 1
             ==>
             l i < l j) /\
          (!i : num.
             i < LENGTH P - 1
             ==>
             (i MOD 4 = 0
              ==>
              FST (EL (i + 1) P) =
                FST (EL i P) + int_of_num (l i) /\
              SND (EL (i + 1) P) = SND (EL i P)) /\
             (i MOD 4 = 1
              ==>
              FST (EL (i + 1) P) = FST (EL i P) /\
              SND (EL (i + 1) P) =
                SND (EL i P) + int_of_num (l i)) /\
             (i MOD 4 = 2
              ==>
              FST (EL (i + 1) P) =
                FST (EL i P) - int_of_num (l i) /\
              SND (EL (i + 1) P) = SND (EL i P)) /\
             (i MOD 4 = 3
              ==>
              FST (EL (i + 1) P) = FST (EL i P) /\
              SND (EL (i + 1) P) =
                SND (EL i P) - int_of_num (l i)))
    in
      CARD
        {p : int # int |
           0 <= FST p /\ FST p <= 2011 /\
           0 <= SND p /\ SND p <= 2011 /\
           ~?spiral : (int # int) list.
             is_spiral spiral /\ LAST spiral = p} =
      10053``;
