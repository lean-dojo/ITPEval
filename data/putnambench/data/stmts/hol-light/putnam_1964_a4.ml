(*
  Statement-only formalization of PutnamBench artifact putnam_1964_a4:
  a bounded integer sequence satisfying the given fourth-order rational
  recurrence is eventually periodic. This file contains no proof.
*)

let statement =
  `!u:num->int.
     (?lo hi:int. !n:num. lo <= u n /\ u n <= hi) /\
     (!n:num.
        4 <= n
        ==> real_of_int (u n) =
            (real_of_int (u (n - 1)) +
             real_of_int (u (n - 2)) +
             real_of_int (u (n - 3)) * real_of_int (u (n - 4))) /
            (real_of_int (u (n - 1)) * real_of_int (u (n - 2)) +
             real_of_int (u (n - 3)) +
             real_of_int (u (n - 4))) /\
            ~(real_of_int (u (n - 1)) * real_of_int (u (n - 2)) +
              real_of_int (u (n - 3)) +
              real_of_int (u (n - 4)) = &0))
     ==> ?N c:num.
           0 < c /\
           !n:num. N <= n ==> u (n + c) = u n`;;
