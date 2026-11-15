(*
  Statement-only formalization of Logipedia corpus artifact
  cong.let_clause_1034, catalog title "cong.let_clause_1034": for arbitrary
  natural numbers n and m and a positive natural number p, every natural
  number has its quotient-remainder decomposition with respect to every
  natural divisor. This file contains no proof.
*)

let statement =
  `!n:num.
   !m:num.
   !p:num.
     0 < p
     ==>
     !x2515:num.
     !x2516:num.
       x2515 = x2515 MOD x2516 + x2516 * (x2515 DIV x2516)`;;
