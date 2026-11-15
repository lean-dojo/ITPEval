(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a6
  (putnambench__hol-light__putnam_2025_a6): exact powers of two dividing a
  difference of terms in a recursively defined integer sequence. This file
  contains no proof.
*)

let statement =
  `!b:num->int.
     b 0 = &0 /\
     (!n:num.
        b (n + 1) =
        (&2:int) * (b n) pow 2 + b n + &1)
     ==>
     !k:num.
       1 <= k
       ==>
       ((&2:int) pow (2 * k + 2)) divides
       (b (2 EXP (k + 1)) - (&2:int) * b (2 EXP k)) /\
       ~(((&2:int) pow (2 * k + 3)) divides
         (b (2 EXP (k + 1)) - (&2:int) * b (2 EXP k)))`;;
