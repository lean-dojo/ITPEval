(*
  Statement-only formalization of PutnamBench artifact putnam_1973_a3:
  the minimum of k + n/k over positive integers k has the same integer part
  as sqrt(4n + 1) for every positive integer n. This file contains no proof.
*)

needs "Library/floor.ml";;

let statement =
  `!b:int->real.
     (!n:int.
        (!k:int.
           (&0:int) < k
           ==> b n <= real_of_int k + real_of_int n / real_of_int k) /\
        (?k:int.
           (&0:int) < k /\
           b n = real_of_int k + real_of_int n / real_of_int k))
     ==> !n:int.
           (&0:int) < n
           ==> floor (b n) =
               floor (sqrt (&4 * real_of_int n + &1))`;;
