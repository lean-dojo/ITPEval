(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_a3:
  every term of the real sequence initialized by three ones and satisfying
  the prescribed factorial determinant recurrence is an integer. This file
  contains no proof.
*)

let statement =
  `!u:num->real.
     (u 0 = &1 /\
      u 1 = &1 /\
      u 2 = &1 /\
      (!n:num.
         u n * u (n + 3) - u (n + 1) * u (n + 2) = &(FACT n)))
     ==> !n:num. ?m:int. u n = real_of_int m`;;
