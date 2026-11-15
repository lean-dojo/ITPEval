(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_b1:
  positive integers h and k admit, for every positive real epsilon, positive
  integer m and n whose weighted square-root difference has absolute value
  strictly between epsilon and twice epsilon. This file contains no proof.
*)

let statement =
  `!h k:int.
     (&0:int) < h /\ (&0:int) < k
     ==>
     !e:real.
       &0 < e
       ==>
       ?m n:int.
         (&0:int) < m /\
         (&0:int) < n /\
         e <
         abs
           (real_of_int h * sqrt (real_of_int m) -
            real_of_int k * sqrt (real_of_int n)) /\
         abs
           (real_of_int h * sqrt (real_of_int m) -
            real_of_int k * sqrt (real_of_int n)) <
         &2 * e`;;
