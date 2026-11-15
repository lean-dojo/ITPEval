(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_b6:
  every positive integer is the endpoint of a finite integer sequence whose
  later terms arise from an earlier term plus a power of two or as a remainder
  of two earlier positive terms. This file contains no proof.
*)

let statement =
  `!n:num.
     0 < n
     ==> ?a:num->int.
           a 0 = &0 /\
           a 2009 = &n /\
           !i:num.
             1 <= i /\ i <= 2009
             ==> (?j k:num.
                    j < i /\
                    a i = a j + (&2:int) pow k) \/
                 (?b c:num.
                    b < i /\
                    c < i /\
                    &0 < a b /\
                    &0 < a c /\
                    a i = a b rem a c)`;;
