(*
  Statement-only formalization of Logipedia corpus artifact
  cong.let_clause_73, catalog title "cong.let_clause_73": for arbitrary
  natural numbers n and m and a positive natural number p, addition of three
  natural numbers is unchanged when the first two summands are exchanged.
  This file contains no proof.
*)

let statement =
  `!n:num.
   !m:num.
   !p:num.
     0 < p
     ==>
     !x134:num.
     !x135:num.
     !x136:num.
       x134 + (x135 + x136) = x135 + (x134 + x136)`;;
