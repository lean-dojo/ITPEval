(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_a4:
  integer 2 by 2 matrices A + kB that are invertible over the integers for
  k = 0 through 4 force A + 5B to be invertible over the integers. This file
  contains no proof.
*)

let statement =
  `let matrix_mul =
     \A:int^2^2. \B:int^2^2.
       (lambda i j.
          isum (1..2) (\k. A$i$k * B$k$j)):int^2^2 in
   let identity_matrix =
     (lambda i j. if i = j then &1 else &0):int^2^2 in
   let matrix_unit =
     \M:int^2^2.
       ?C:int^2^2.
         matrix_mul M C = identity_matrix /\
         matrix_mul C M = identity_matrix in
   let affine_matrix =
     \k:num. \A:int^2^2. \B:int^2^2.
       (lambda i j. A$i$j + &k * B$i$j):int^2^2 in
   !A:int^2^2. !B:int^2^2.
     matrix_unit (affine_matrix 0 A B) /\
     matrix_unit (affine_matrix 1 A B) /\
     matrix_unit (affine_matrix 2 A B) /\
     matrix_unit (affine_matrix 3 A B) /\
     matrix_unit (affine_matrix 4 A B)
     ==> matrix_unit (affine_matrix 5 A B)`;;
