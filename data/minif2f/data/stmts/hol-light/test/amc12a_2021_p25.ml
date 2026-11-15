(*
  Statement-only formalization of miniF2F test problem amc12a_2021_p25:
  the positive maximizer of divisor count divided by the real cube root
  has decimal digit sum 9. This file contains no proof.
*)

let statement =
  `!N:num f:num->real.
     0 < N /\
     (!n:num.
        0 < n
        ==> f n =
            &(CARD {k:num | k divides n}) /
            exp (&1 / &3 * ln (&n))) /\
     (!p:num. ~(p = N) /\ 0 < p ==> f p < f N)
     ==>
     ?k:num d:num->num.
       (!i. i < k ==> d i < 10) /\
       N = nsum {i | i < k} (\i. 10 EXP i * d i) /\
       nsum {i | i < k} d = 9`;;
