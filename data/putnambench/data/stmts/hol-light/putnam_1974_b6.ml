(*
  Statement-only formalization of PutnamBench artifact putnam_1974_b6:
  counts of subsets of {1,...,1000} in each cardinality residue class
  modulo 3. This file contains no proof.
*)

let statement =
  `let count0 =
     CARD {S:num->bool |
             S SUBSET (1..1000) /\ CARD S MOD 3 = 0} in
   let count1 =
     CARD {S:num->bool |
             S SUBSET (1..1000) /\ CARD S MOD 3 = 1} in
   let count2 =
     CARD {S:num->bool |
             S SUBSET (1..1000) /\ CARD S MOD 3 = 2} in
   let common = (2 EXP 1000 - 1) DIV 3 in
   (count0,count1,count2) = (common,common,common + 1)`;;
