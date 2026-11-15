(*
  Statement-only formalization of miniF2F test problem numbertheory_exk2powkeqapb2mulbpa2_aeq1.
  This file contains no proof.
*)

let statement =
  `!a b:num.
     0 < a /\ 0 < b /\
     (?k:num. 0 < k /\
              2 EXP k = (a + b EXP 2) * (b + a EXP 2))
     ==> a = 1`;;
