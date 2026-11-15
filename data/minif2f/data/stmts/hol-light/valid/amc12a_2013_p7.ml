(*
  Statement-only formalization of miniF2F valid problem amc12a_2013_p7:
  a real sequence satisfying the Fibonacci recurrence, with terms 9 and 7 fixed,
  has term 4 equal to 10. This file contains no proof.
*)

let amc12a_2013_p7 =
  `!s:num->real.
     (!n:num. s (n + 2) = s (n + 1) + s n) /\
     s 9 = &110 /\
     s 7 = &42
     ==> s 4 = &10`;;
