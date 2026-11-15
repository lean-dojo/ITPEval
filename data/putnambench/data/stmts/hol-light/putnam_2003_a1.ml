(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_a1:
  the number of nonempty nondecreasing lists of positive integers summing to
  n, with last entry at most one more than the first, is n. This file contains
  no proof.
*)

let statement =
  `!n:num.
     0 < n
     ==>
     CARD
       {a:num list |
          ~(a = []) /\
          nsum (0..LENGTH a - 1) (\i. EL i a) = n /\
          (!i:num. i < LENGTH a ==> 0 < EL i a) /\
          (!i:num.
             i + 1 < LENGTH a
             ==> EL i a <= EL (i + 1) a) /\
          LAST a <= HD a + 1} =
     n`;;
