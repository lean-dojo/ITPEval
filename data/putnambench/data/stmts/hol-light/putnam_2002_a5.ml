(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_a5:
  the binary-recursive rational sequence yields every positive rational as
  a ratio of consecutive terms. This file contains no proof.
*)

let statement =
  `let is_rat =
     \x:real.
       ?p:int q:num.
         ~(q = 0) /\
         x = real_of_int p / &q in
   !a:num->real.
     (!k:num. is_rat (a k)) /\
     a 0 = &1 /\
     (!n:num.
        a (2 * n + 1) = a n /\
        a (2 * n + 2) = a n + a (n + 1))
     ==>
     !q:real.
       is_rat q /\ &0 < q
       ==> ?n:num.
             1 <= n /\
             q = a (n - 1) / a n`;;
