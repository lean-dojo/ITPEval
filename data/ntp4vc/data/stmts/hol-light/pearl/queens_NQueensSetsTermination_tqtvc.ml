(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/queens_NQueensSetsTermination_tqtvc: the finite-set termination
  verification condition for the recursive N-queens search, including strict
  decreases of the board and loop-candidate cardinalities. This file contains
  no proof.
*)

let queens_NQueensSetsTermination_tqtvc_statement =
  `!a o1 b o2 c:int->bool.
     FINITE a /\
     FINITE o1 /\
     FINITE b /\
     FINITE o2 /\
     FINITE c /\
     ~(a = {}) /\
     o1 = a DIFF b /\
     o2 = o1 DIFF c
     ==>
     (o2 SUBSET (a DIFF b) DIFF c /\
      !f:int.
      !e:int->bool.
        FINITE e /\
        e SUBSET (a DIFF b) DIFF c /\
        ~(e = {})
        ==>
        (~(e = {}) /\
         let d =
           @d:int. d IN e /\ (!x:int. x IN e ==> d <= x) in
         !o3:int->bool.
           FINITE o3 /\
           o3 = d INSERT c /\
           (if d IN c then
              CARD o3 = CARD c
            else
              (&(CARD o3):int) =
              (&(CARD c):int) + (&1:int))
           ==>
           !o4:int->bool.
             FINITE o4 /\
             (!i:int.
                i IN o4 <=>
                (&0:int) <= i /\ i + (&1:int) IN o3)
             ==>
             !o5:int->bool.
               FINITE o5 /\
               o5 = d INSERT b /\
               (if d IN b then
                  CARD o5 = CARD b
                else
                  (&(CARD o5):int) =
                  (&(CARD b):int) + (&1:int))
               ==>
               !o6:int->bool.
                 FINITE o6 /\
                 (!i:int.
                    i IN o6 <=>
                    (&1:int) <= i /\ i - (&1:int) IN o5)
                 ==>
                 !o7:int->bool.
                   FINITE o7 /\
                   o7 = a DELETE d /\
                   (if d IN a then
                      (&(CARD o7):int) =
                      (&(CARD a):int) - (&1:int)
                    else
                      CARD o7 = CARD a)
                   ==>
                   (((&0:int) <= (&(CARD a):int) /\
                     (&(CARD o7):int) < (&(CARD a):int)) /\
                    !o8:int.
                    !o9:int->bool.
                      FINITE o9 /\
                      o9 = e DELETE d /\
                      (if d IN e then
                         (&(CARD o9):int) =
                         (&(CARD e):int) - (&1:int)
                       else
                         CARD o9 = CARD e)
                      ==>
                      (((&0:int) <= (&(CARD e):int) /\
                        (&(CARD o9):int) < (&(CARD e):int)) /\
                       o9 SUBSET (a DIFF b) DIFF c))))`;;
