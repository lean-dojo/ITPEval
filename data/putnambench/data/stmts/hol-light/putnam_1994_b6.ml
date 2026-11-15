(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_b6:
  uniqueness of unordered pairs of indices from 0 through 99 whose associated
  sequence values have equal sums modulo 10100. This file contains no proof.
*)

let statement =
  `!n:num->int.
     (!a:num.
        n a = (&101:int) * &a - (&100:int) * ((&2:int) pow a))
     ==>
     !a b c d:num.
       a <= 99 /\ b <= 99 /\ c <= 99 /\ d <= 99 /\
       (n a + n b == n c + n d) (mod (&10100:int))
       ==> {a,b} = {c,d}`;;
