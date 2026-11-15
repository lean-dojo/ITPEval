(*
  Statement-only formalization of miniF2F test problem amc12a_2008_p25. This file contains no
  proof.
*)

let statement =
  `!a b:num->real.
     ((!n:num. a (n + 1) = sqrt (&3) * a n - b n) /\
      (!n:num. b (n + 1) = sqrt (&3) * b n + a n) /\
      a 100 = &2 /\
      b 100 = &4)
     ==> a 1 + b 1 = &1 / (&2 pow 98)`;;
