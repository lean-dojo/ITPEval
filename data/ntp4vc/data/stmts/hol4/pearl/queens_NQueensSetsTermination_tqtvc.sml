(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/queens_NQueensSetsTermination_tqtvc: the finite integer-set
  N-queens termination verification condition, including residual-set
  containment and strict cardinality decreases after removing a selected
  minimum element. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory pred_setTheory;

val queens_min_def = Define `
  queens_min (e : int set) =
    @d : int.
      d IN e /\
      !x : int. x IN e ==> d <= x`;

val queens_NQueensSetsTermination_t_vc =
  ``!(a : int set)
      (o1 : int set)
      (b : int set)
      (o2 : int set)
      (c : int set).
      FINITE a /\
      FINITE o1 /\
      FINITE b /\
      FINITE o2 /\
      FINITE c /\
      a <> {} /\
      o1 = a DIFF b /\
      o2 = o1 DIFF c
      ==>
      o2 SUBSET ((a DIFF b) DIFF c) /\
      !f : int.
      !e : int set.
        FINITE e ==>
        e SUBSET ((a DIFF b) DIFF c) ==>
        e <> {} ==>
        e <> {} /\
        let d = queens_min e
        in
          !o3 : int set.
            FINITE o3 ==>
            o3 = d INSERT c /\
            (if d IN c then
               CARD o3 = CARD c
             else
               &(CARD o3) = &(CARD c) + (1 : int))
            ==>
            !o4 : int set.
              FINITE o4 ==>
              (!i : int.
                 i IN o4 <=>
                 (0 : int) <= i /\ i + (1 : int) IN o3)
              ==>
              !o5 : int set.
                FINITE o5 ==>
                o5 = d INSERT b /\
                (if d IN b then
                   CARD o5 = CARD b
                 else
                   &(CARD o5) = &(CARD b) + (1 : int))
                ==>
                !o6 : int set.
                  FINITE o6 ==>
                  (!i : int.
                     i IN o6 <=>
                     (1 : int) <= i /\ i - (1 : int) IN o5)
                  ==>
                  !o7 : int set.
                    FINITE o7 ==>
                    o7 = a DELETE d /\
                    (if d IN a then
                       &(CARD o7) = &(CARD a) - (1 : int)
                     else
                       CARD o7 = CARD a)
                    ==>
                    ((0 : int) <= &(CARD a) /\
                     CARD o7 < CARD a) /\
                    !o8 : int.
                    !o9 : int set.
                      FINITE o9 ==>
                      o9 = e DELETE d /\
                      (if d IN e then
                         &(CARD o9) = &(CARD e) - (1 : int)
                       else
                         CARD o9 = CARD e)
                      ==>
                      ((0 : int) <= &(CARD e) /\
                       CARD o9 < CARD e) /\
                      o9 SUBSET ((a DIFF b) DIFF c)``;
