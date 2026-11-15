(*
  Statement-only formalization of PutnamBench artifact putnam_1962_b5:
  for every natural n greater than one, the sum of (i/n)^n from i = 1
  through n lies strictly between (3n+1)/(2n+2) and 2. This file contains
  no proof.

  The published problem quantifies over integers n > 1. Such an n is
  necessarily natural, so the natural-number indexing used here is
  equivalent while matching HOL Light's finite interval and power APIs.
*)

let statement =
  `!n:num.
     1 < n
     ==>
     (&3 * &n + &1) / (&2 * &n + &2) <
       sum (1..n) (\i:num. (&i / &n) pow n) /\
     sum (1..n) (\i:num. (&i / &n) pow n) < &2`;;
