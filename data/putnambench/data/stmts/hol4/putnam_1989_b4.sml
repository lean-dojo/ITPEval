(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_b4:
  an uncountable collection of nonempty subsets of the natural numbers whose
  distinct members have finite intersection. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val putnam_1989_b4 =
  ``let putnam_1989_b4_solution = T
    in
      ((?C : (num set) set.
          ~countable C /\
          (!R : num set.
             R IN C ==> R <> {}) /\
          (!A B : num set.
             A IN C /\ B IN C /\ A <> B
             ==>
             FINITE (A INTER B)))
       <=>
       putnam_1989_b4_solution)``;
