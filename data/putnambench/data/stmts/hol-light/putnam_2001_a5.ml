(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_a5:
  uniqueness of the positive integers a and n satisfying
  a^(n+1) - (a+1)^n = 2001. This file contains no proof.
*)

let statement =
  `?!(a,n):int#num.
     (&0:int) < a /\
     0 < n /\
     a pow (n + 1) - (a + &1) pow n = &2001`;;
