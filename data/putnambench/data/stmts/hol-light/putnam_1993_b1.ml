(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_b1:
  the smallest positive integer n such that every integer m with 0 < m < 1993
  admits an integer k with m/1993 < k/n < (m+1)/1994 is 3987.
  This file contains no proof.
*)

let statement =
  `let admissible =
     \n:num.
       0 < n /\
       (!m:int.
          (&0:int) < m /\ m < (&1993:int)
          ==> ?k:int.
                real_of_int m / &1993 < real_of_int k / &n /\
                real_of_int k / &n <
                real_of_int (m + (&1:int)) / &1994) in
   admissible 3987 /\
   (!n:num. admissible n ==> 3987 <= n)`;;
