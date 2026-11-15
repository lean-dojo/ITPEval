(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_a4:
  an integer-labeled necklace of positive length and total label sum one less
  than its length has a cut whose inclusive partial sums are suitably bounded.
  This file contains no proof.
*)

let statement =
  `!n:num. !necklace:num->int.
     0 < n /\
     isum (0..n - 1) necklace = &n - &1
     ==>
     ?cut:num.
       cut < n /\
       !k:num.
         k < n
         ==> isum (0..k) (\i. necklace ((cut + i) MOD n)) <= &k`;;
