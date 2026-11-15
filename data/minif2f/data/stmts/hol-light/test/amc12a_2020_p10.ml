(*
  Statement-only formalization of miniF2F test problem amc12a_2020_p10:
  every natural solution greater than one has decimal digit sum 13.
  A bounded base-ten expansion represents the digit sum natively.
  This file contains no proof.
*)

let statement =
  `!n:num.
     1 < n /\
     ln (ln (&n) / ln (&16)) / ln (&2) =
       ln (ln (&n) / ln (&4)) / ln (&4)
     ==>
     ?k:num d:num->num.
       (!i. i < k ==> d i < 10) /\
       n = nsum {i | i < k} (\i. 10 EXP i * d i) /\
       nsum {i | i < k} d = 13`;;
