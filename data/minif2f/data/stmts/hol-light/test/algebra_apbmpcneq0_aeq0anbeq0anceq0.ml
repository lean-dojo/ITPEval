(*
  Statement-only formalization of miniF2F test problem algebra_apbmpcneq0_aeq0anbeq0anceq0. This
  file contains no proof.
*)

let statement =
  `!a b c m n:real.
    rational a /\ rational b /\ rational c /\
    &0 < m /\ &0 < n /\
    m pow 3 = &2 /\
    n pow 3 = &4 /\
    a + b * m + c * n = &0
    ==> a = &0 /\ b = &0 /\ c = &0`;;
