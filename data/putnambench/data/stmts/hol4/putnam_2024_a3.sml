(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a3:
  existence of two positions in a 3 by 2024 increasing bijective array for
  which the comparison holds in between one third and two thirds of all such
  arrays. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory;

val putnam_2024_a3 =
  ``let rows = {i : num | 1 <= i /\ i <= 3};
        cols = {j : num | 1 <= j /\ j <= 2024};
        values = {n : num | 1 <= n /\ n <= 6072};
        grid = rows CROSS cols;
        S =
          {T : (num # num) -> num |
             BIJ T grid values /\
             (!j : num.
                j IN cols
                ==>
                !i k : num.
                  i IN rows /\ k IN rows /\ i < k
                  ==>
                  T (i,j) < T (k,j)) /\
             (!i : num.
                i IN rows
                ==>
                !j k : num.
                  j IN cols /\ k IN cols /\ j < k
                  ==>
                  T (i,j) < T (i,k)) /\
             (!x : num # num. x NOTIN grid ==> T x = 0)}
    in
      ?a b c d : num.
        a IN rows /\ b IN cols /\ c IN rows /\ d IN cols /\
        (1 : real) / 3 <=
          (&(CARD {T : (num # num) -> num |
                     T IN S /\ T (a,b) < T (c,d)}) : real) /
          (&(CARD S) : real) /\
        (&(CARD {T : (num # num) -> num |
                   T IN S /\ T (a,b) < T (c,d)}) : real) /
          (&(CARD S) : real) <=
        (2 : real) / 3``;
