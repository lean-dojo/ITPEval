(*
  Statement-only formalization of PutnamBench artifact putnam_1978_a1:
  every 20-element subset of the integers 1, 4, 7, ..., 100 contains two
  distinct elements whose sum is 104. This file contains no proof.
*)

let statement =
  `!s t:int->bool.
     s =
       {k:int |
          ?j:int.
            (&0:int) <= j /\
            j <= &33 /\
            k = &3 * j + &1} /\
     t SUBSET s /\
     CARD t = 20
     ==> ?m n:int.
           m IN t /\
           n IN t /\
           ~(m = n) /\
           m + n = &104`;;
