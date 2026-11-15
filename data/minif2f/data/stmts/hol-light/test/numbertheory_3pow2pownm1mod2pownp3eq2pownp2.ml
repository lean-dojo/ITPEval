(*
  Statement-only formalization of miniF2F test problem
  numbertheory_3pow2pownm1mod2pownp3eq2pownp2. This file contains no proof.
*)

let statement =
  `!n:num. 0 < n ==>
    (3 EXP (2 EXP n) - 1) MOD (2 EXP (n + 3)) = 2 EXP (n + 2)`;;
