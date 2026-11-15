(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_b1:
  the number of minimal selfish subsets of {1,...,n}, where a set is selfish
  when it contains its own cardinality, is the nth Fibonacci number. This file
  contains no proof.
*)

let statement =
  `!putnam_1996_b1_solution:num->num.
     putnam_1996_b1_solution 0 = 0 /\
     putnam_1996_b1_solution 1 = 1 /\
     (!m:num.
        putnam_1996_b1_solution (m + 2) =
        putnam_1996_b1_solution m +
        putnam_1996_b1_solution (m + 1))
     ==>
     !n:num.
       1 <= n
       ==>
       CARD
         {s:num->bool |
            s SUBSET (1..n) /\
            CARD s IN s /\
            (!ss:num->bool.
               ss PSUBSET s ==> ~(CARD ss IN ss))} =
       putnam_1996_b1_solution n`;;
