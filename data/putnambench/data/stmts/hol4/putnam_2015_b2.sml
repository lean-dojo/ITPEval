(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_b2:
  the iterative process that crosses off the three least remaining positive
  integers and their sum produces a sum ending in the decimal digits 2015.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_2015_b2 =
  ``let putnam_2015_b2_solution = T
    in
      !(sets : num -> num set)
       (Smin3 : num set -> num # (num # num))
       (sums : num -> num).
        let first = \S : num set. FST (Smin3 S) in
        let second = \S : num set. FST (SND (Smin3 S)) in
        let third = \S : num set. SND (SND (Smin3 S)) in
          sets 0 = {n : num | 1 <= n} /\
          (!S : num set.
             (INFINITE S \/ 3 <= CARD S)
             ==>
             first S = (LEAST x : num. x IN S) /\
             second S = (LEAST x : num. x IN S DELETE first S) /\
             third S =
               (LEAST x : num.
                  x IN (S DELETE first S) DELETE second S)) /\
          (!n : num.
             sums n = first (sets n) + second (sets n) + third (sets n)) /\
          (!n : num.
             sets (n + 1) =
               (((sets n DELETE first (sets n))
                   DELETE second (sets n))
                  DELETE third (sets n))
                 DELETE sums n)
          ==>
          ((?n : num. sums n MOD 10000 = 2015) <=>
           putnam_2015_b2_solution)``;
