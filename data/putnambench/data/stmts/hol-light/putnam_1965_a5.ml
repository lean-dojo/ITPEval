(*
  Statement-only formalization of PutnamBench artifact putnam_1965_a5:
  the number of orderings of 1 through n in which every entry after the
  first differs by one from some earlier entry. This file contains no proof.
*)

let statement =
  `!n:num.
     0 < n
     ==> CARD
           {p:num->num |
              BIJ p (1..n) (1..n) /\
              (!i:num. ~(i IN 1..n) ==> p i = 0) /\
              (!m:num.
                 2 <= m /\ m <= n
                 ==> ?k:num.
                       1 <= k /\ k < m /\
                       (p m = p k + 1 \/ p k = p m + 1))} =
         2 EXP (n - 1)`;;
