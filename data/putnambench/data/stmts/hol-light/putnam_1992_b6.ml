(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_b6:
  signed closure, commutation or anticommutation, and the cardinality bound
  for a set of real square matrices. This file contains no proof.
*)

let statement =
  `let matrix_mul =
     \A B:real^N^N.
       (lambda i j.
          sum (1..dimindex(:N)) (\k. A$i$k * B$k$j)):real^N^N in
   let matrix_neg =
     \A:real^N^N.
       (lambda i j. --(A$i$j)):real^N^N in
   let identity_matrix =
     (lambda i j. if i = j then &1 else &0):real^N^N in
   let exclusive_or =
     \p q:bool. (p \/ q) /\ ~(p /\ q) in
   !n:num. !M:(real^N^N)->bool.
     dimindex(:N) = n /\
     0 < n /\
     identity_matrix IN M /\
     (!A:real^N^N.
        A IN M
        ==> !B:real^N^N.
              B IN M
              ==> exclusive_or
                    (matrix_mul A B IN M)
                    (matrix_neg (matrix_mul A B) IN M)) /\
     (!A:real^N^N.
        A IN M
        ==> !B:real^N^N.
              B IN M
              ==> matrix_mul A B = matrix_mul B A \/
                  matrix_mul A B = matrix_neg (matrix_mul B A)) /\
     (!A:real^N^N.
        A IN M /\ ~(A = identity_matrix)
        ==> ?B:real^N^N.
              B IN M /\
              matrix_mul A B = matrix_neg (matrix_mul B A))
     ==> FINITE M /\ CARD M <= n EXP 2`;;
