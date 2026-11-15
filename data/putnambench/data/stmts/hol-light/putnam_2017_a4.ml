(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_a4
  (putnambench__hol-light__putnam_2017_a4): partitioning 2N quiz scores from
  0 through 10, each occurring, into two N-student groups with the same
  average 74/10 as the whole class. This file contains no proof.
*)

let statement =
  `!N:num. !score:num->num.
     (!i:num. i < 2 * N ==> score i < 11) /\
     (!k:num. k < 11 ==> ?i:num. i < 2 * N /\ score i = k) /\
     sum {i:num | i < 2 * N} (\i. &(score i)) / &(2 * N) =
       &74 / &10
     ==>
     ?S:num->bool.
       S SUBSET {i:num | i < 2 * N} /\
       S HAS_SIZE N /\
       sum S (\i. &(score i)) / &N = &74 / &10 /\
       sum ({i:num | i < 2 * N} DIFF S) (\i. &(score i)) / &N =
         &74 / &10`;;
