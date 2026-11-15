(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_b6:
  a finite group of real square matrices has zero matrix sum when the sum of
  the matrices' traces is zero. This file contains no proof.
*)

let statement =
  `let matrix_mul =
     \A B:real^N^N.
       (lambda i j.
          sum (1..dimindex(:N)) (\k. A$i$k * B$k$j)):real^N^N in
   let identity_matrix =
     (lambda i j. if i = j then &1 else &0):real^N^N in
   let zero_matrix =
     (lambda i j. &0):real^N^N in
   let matrix_trace =
     \A:real^N^N. sum (1..dimindex(:N)) (\i. A$i$i) in
   let matrix_sum =
     \G:(real^N^N)->bool.
       (lambda i j. sum G (\M:real^N^N. M$i$j)):real^N^N in
   !n:num. !G:(real^N^N)->bool.
     dimindex(:N) = n /\
     0 < n /\
     FINITE G /\
     (!g:real^N^N.
        g IN G ==> !h:real^N^N. h IN G ==> matrix_mul g h IN G) /\
     identity_matrix IN G /\
     (!g:real^N^N.
        g IN G
        ==> ?h:real^N^N.
              h IN G /\ matrix_mul g h = identity_matrix) /\
     sum G matrix_trace = &0
     ==> matrix_sum G = zero_matrix`;;
