(*
  Statement-only formalization of miniF2F valid problem amc12a_2017_p7. This file contains no
  proof.
*)

let amc12a_2017_p7 =
  `!f:num->real.
     f 1 = &2 /\
     (!n:num. 1 < n /\ EVEN n
              ==> f n = f (n - 1) + &1) /\
     (!n:num. 1 < n /\ ODD n
              ==> f n = f (n - 2) + &2)
     ==> f 2017 = &2018`;;
