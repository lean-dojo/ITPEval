(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_a4:
  the last two decimal digits occurring infinitely often in the sequence
  a_1 = 3, a_(i+1) = 3^(a_i). This file contains no proof.
*)

let statement =
  `!a:num->num.
     a 1 = 3 /\
     (!i:num. 1 <= i ==> a (i + 1) = 3 EXP (a i))
     ==> {k:num |
            k < 100 /\
            !N:num. ?i:num. N <= i /\ a i MOD 100 = k} =
         {87}`;;
