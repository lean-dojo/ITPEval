(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_a3:
  the universal claim that among twenty students choosing from six courses,
  five students all chose two common courses or all omitted them is false.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1996_a3 =
  ``let putnam_1996_a3_solution = F
    in
      ((!choices : num -> num set.
          (!s : num. s < 20 ==> choices s SUBSET count 6)
          ==>
          ?students courses : num set.
            students SUBSET count 20 /\
            CARD students = 5 /\
            courses SUBSET count 6 /\
            CARD courses = 2 /\
            ((!s c : num.
                s IN students /\ c IN courses
                ==>
                c IN choices s) \/
             (!s c : num.
                s IN students /\ c IN courses
                ==>
                c NOTIN choices s)))
       <=> putnam_1996_a3_solution)``;
