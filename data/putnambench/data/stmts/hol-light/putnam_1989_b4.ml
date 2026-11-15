(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_b4:
  existence of an uncountable family of nonempty subsets of a countably
  infinite set whose distinct members have finite intersection. This file
  contains no proof.
*)

let statement =
  `let putnam_1989_b4_solution = T in
   ((?C:(num->bool)->bool.
       ~COUNTABLE C /\
       (!R:num->bool. R IN C ==> ~(R = {})) /\
       (!A B:num->bool.
          A IN C /\ B IN C /\ ~(A = B)
          ==> FINITE (A INTER B)))
    <=> putnam_1989_b4_solution)`;;
