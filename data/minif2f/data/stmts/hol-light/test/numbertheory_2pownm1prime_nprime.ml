(*
  Statement-only formalization of miniF2F test problem numbertheory_2pownm1prime_nprime. This
  file contains no proof.
*)

let statement =
  `!n:num.
     0 < n /\ prime (2 EXP n - 1)
     ==> prime n`;;
