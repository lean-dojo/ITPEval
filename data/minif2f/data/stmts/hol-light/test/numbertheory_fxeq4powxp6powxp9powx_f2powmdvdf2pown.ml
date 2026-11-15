(*
  Statement-only formalization of miniF2F test problem
  numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown. This file contains no proof.
*)

let statement =
  `!m n:num. !f:num->num.
     (!x:num. f x = 4 EXP x + 6 EXP x + 9 EXP x) /\
     (0 < m /\ 0 < n) /\
     m <= n
     ==> f (2 EXP m) divides f (2 EXP n)`;;
