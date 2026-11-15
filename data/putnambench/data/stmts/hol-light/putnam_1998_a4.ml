(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_a4:
  the indices whose recursively concatenated decimal strings are divisible
  by 11 are exactly those congruent to 1 modulo 6. This file contains no proof.
*)

let statement =
  `let from_digits =
     \ds:num list. ITLIST (\d acc. d + 10 * acc) ds 0 in
   !A:num->num list.
     A 1 = [0] /\
     A 2 = [1] /\
     (!n:num.
        0 < n
        ==> A (n + 2) = APPEND (A (n + 1)) (A n))
     ==>
     {n:num | 1 <= n /\ 11 divides from_digits (A n)} =
     {n:num | n MOD 6 = 1}`;;
