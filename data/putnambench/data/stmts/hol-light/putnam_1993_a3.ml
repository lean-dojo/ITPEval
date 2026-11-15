(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_a3:
  the number of functions from the subsets of an n-element set to
  {1,...,m} that send intersections to minima is sum_{j=1}^m j^n.
  This file contains no proof.
*)

let statement =
  `!n m:num.
     1 <= n /\ 1 <= m
     ==>
     CARD
       {f:(num->bool)->num |
          (!A:num->bool.
             A SUBSET (1..n)
             ==> 1 <= f A /\ f A <= m) /\
          (!A:num->bool.
             ~(A SUBSET (1..n))
             ==> f A = 0) /\
          (!A B:num->bool.
             A SUBSET (1..n) /\ B SUBSET (1..n)
             ==> f (A INTER B) = MIN (f A) (f B))} =
     nsum (1..m) (\j:num. j EXP n)`;;
