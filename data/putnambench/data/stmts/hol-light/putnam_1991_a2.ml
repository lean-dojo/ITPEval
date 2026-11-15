(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_a2:
  in every positive dimension, no two distinct real square matrices satisfying
  A^3 = B^3 and A^2 B = B^2 A have an invertible sum A^2 + B^2. This file
  contains no proof.
*)

let statement =
  `let matrix_mul =
     \A B:real^N^N.
       (lambda i j.
          sum (1..dimindex(:N)) (\k. A$i$k * B$k$j)):real^N^N in
   let matrix_add =
     \A B:real^N^N.
       (lambda i j. A$i$j + B$i$j):real^N^N in
   let matrix_square =
     \A:real^N^N. matrix_mul A A in
   let matrix_cube =
     \A:real^N^N. matrix_mul (matrix_square A) A in
   let identity_matrix =
     (lambda i j. if i = j then &1 else &0):real^N^N in
   let matrix_invertible =
     \A:real^N^N.
       ?C:real^N^N.
         matrix_mul A C = identity_matrix /\
         matrix_mul C A = identity_matrix in
   !n:num.
     dimindex(:N) = n /\
     0 < n
     ==>
     ~(?A B:real^N^N.
         ~(A = B) /\
         matrix_cube A = matrix_cube B /\
         matrix_mul (matrix_square A) B =
         matrix_mul (matrix_square B) A /\
         matrix_invertible
           (matrix_add (matrix_square A) (matrix_square B)))`;;
