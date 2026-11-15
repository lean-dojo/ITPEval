(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_b5:
  the number of length-n strings of two symbols whose every consecutive
  substring has symbol-count difference between -2 and 2. This file contains
  no proof.
*)

let statement =
  `!n:num.
     let delta =
       \S:num->bool. \a b:num.
         isum (a..b)
           (\i. if S i then (&1:int) else --(&1:int)) in
     let balanced =
       \S:num->bool.
         !a b:num.
           a < n /\ b < n /\ a <= b
           ==> --(&2:int) <= delta S a b /\
               delta S a b <= &2 in
     CARD
       {S:num->bool |
          balanced S /\
          (!i:num. n <= i ==> S i = F)} =
     2 EXP ((n + 2) DIV 2) +
     2 EXP ((n + 1) DIV 2) - 2`;;
