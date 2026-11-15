(*
  Statement-only formalization of PutnamBench artifact putnam_1976_a3:
  classification of prime powers whose integer absolute difference is one.
  This file contains no proof.
*)

let statement =
  `!p r q s:num.
     (prime p /\ prime q /\ r > 1 /\ s > 1 /\
      abs ((&(p EXP r):int) - &(q EXP s)) = &1)
     <=>
     (p = 3 /\ r = 2 /\ q = 2 /\ s = 3) \/
     (p = 2 /\ r = 3 /\ q = 3 /\ s = 2)`;;
