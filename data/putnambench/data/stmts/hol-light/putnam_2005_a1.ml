(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_a1:
  every positive integer is a sum of numbers of the form 2^r * 3^s with
  nonnegative exponents, no one summand dividing another. This file contains
  no proof.
*)

let statement =
  `!n:num.
     0 < n
     ==>
     ?k:num. ?a:num->num#num.
       nsum (0..k - 1)
         (\i. 2 EXP (FST (a i)) * 3 EXP (SND (a i))) =
       n /\
       (!i j:num.
          i < k /\ j < k /\ ~(i = j)
          ==>
          ~(2 EXP (FST (a i)) * 3 EXP (SND (a i)) divides
            2 EXP (FST (a j)) * 3 EXP (SND (a j))))`;;
