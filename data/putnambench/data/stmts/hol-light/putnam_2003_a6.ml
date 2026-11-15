(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_a6:
  existence of a partition of the nonnegative integers into two sets having
  equal counts of distinct ordered summand pairs for every sum. This file
  contains no proof.
*)

let statement =
  `(?A B:num->bool.
      A UNION B = (:num) /\
      A INTER B = {} /\
      (!n:num.
         CARD
           {(s1,s2):num#num |
              s1 IN A /\ s2 IN A /\ ~(s1 = s2) /\ s1 + s2 = n} =
         CARD
           {(s1,s2):num#num |
              s1 IN B /\ s2 IN B /\ ~(s1 = s2) /\ s1 + s2 = n}))
   <=> T`;;
