(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_a6:
  every positive-indexed term of the specified nonlinear real recurrence is
  an integer multiple of its index. This file contains no proof.
*)

let statement =
  `!a:num->real.
     a 1 = &1 /\
     a 2 = &2 /\
     a 3 = &24 /\
     (!n:num.
        4 <= n
        ==> a n =
            (&6 * (a (n - 1)) pow 2 * a (n - 3) -
             &8 * a (n - 1) * (a (n - 2)) pow 2) /
            (a (n - 2) * a (n - 3)))
     ==> !n:num.
           1 <= n
           ==> ?k:int. a n = real_of_int k * &n`;;
