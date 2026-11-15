(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_b5:
  the number of permutations of {1,...,n} that send adjacent positions to
  values at distance at most two satisfies a constant recurrence of value 4.
  This file contains no proof.
*)

let statement =
  `let P =
     \n:num.
       CARD
         {p:num->num |
            BIJ p (1..n) (1..n) /\
            (!i:num. ~(i IN 1..n) ==> p i = i) /\
            (!i j:num.
               i IN 1..n /\
               j IN 1..n /\
               (i + 1 = j \/ j + 1 = i)
               ==> p i <= p j + 2 /\ p j <= p i + 2)} in
   !n:num.
     2 <= n
     ==>
     (&(P (n + 5)):int) -
     (&(P (n + 4)):int) -
     (&(P (n + 3)):int) +
     (&(P n):int) =
     (&4:int)`;;
