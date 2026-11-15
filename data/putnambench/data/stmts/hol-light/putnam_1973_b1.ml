(*
  Statement-only formalization of PutnamBench artifact putnam_1973_b1:
  equal-sum bipartitions after removing any one of 2n+1 indexed integers
  imply that all the integers are equal. This file contains no proof.
*)

let statement =
  `!n:num. !a:num->int.
     (!S:num->bool.
        S SUBSET (1..(2 * n + 1)) /\
        CARD S = 2 * n
        ==> ?t:num->bool.
              t SUBSET S /\
              CARD t = n /\
              isum t a = isum (S DIFF t) a)
     ==> !i j:num.
           i IN (1..(2 * n + 1)) /\
           j IN (1..(2 * n + 1))
           ==> a i = a j`;;
