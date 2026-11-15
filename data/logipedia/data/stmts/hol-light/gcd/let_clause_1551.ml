(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1551, catalog title "gcd.let_clause_1551": for arbitrary
  natural numbers m and n, if n is zero, then n equals every natural multiple
  of n. This file contains no proof.
*)

let statement =
  `!m:num. !n:num.
     0 = n
     ==> !x347:num.
           n = x347 * n`;;
