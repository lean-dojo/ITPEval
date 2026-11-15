(*
  Statement-only formalization of Logipedia corpus artifact
  primes.let_clause_15311, catalog title "primes.let_clause_15311": for
  natural numbers n, m, d, and p, if m is positive and divisible by n, then
  m being n times the successor of p implies that m is n plus n times p.
  This file contains no proof.
*)

let statement =
  `!n m:num.
     0 < m
     ==> n divides m
     ==> !d:num.
           !p:num.
             m = n * SUC p
             ==> m = n + n * p`;;
