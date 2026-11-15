(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b4
  (putnambench__hol-light__putnam_2025_b4): an upper bound on the sum of a
  nonnegative-integer square matrix with a triangular zero region and entries
  increasing by zero or one along rows and columns. This file contains no
  proof.
*)

let statement =
  `!m:num.
   !A:num->num->num.
   !S N:num.
     let grid = 0..m+1 in
     let steps = 0..m in
     (!i j:num.
        i IN grid /\ j IN grid /\ i + j <= m
        ==> A i j = 0) /\
     (!i j:num.
        i IN steps /\ j IN grid
        ==> A (i + 1) j = A i j \/
            A (i + 1) j = A i j + 1) /\
     (!i j:num.
        i IN grid /\ j IN steps
        ==> A i (j + 1) = A i j \/
            A i (j + 1) = A i j + 1) /\
     S = nsum grid (\i. nsum grid (\j. A i j)) /\
     N = CARD {(i,j) | i IN grid /\ j IN grid /\ ~(A i j = 0)}
     ==>
     3 * S <= (m + 4) * N`;;
