(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_b4:
  no real 2 by 2 matrix has matrix sine equal to the upper triangular matrix
  with diagonal entries 1 and upper-right entry 1996. This file contains no
  proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let matrix_mul =
     \A B:real^2^2.
       (lambda i j. sum (1..2) (\k. A$i$k * B$k$j)):real^2^2 in
   let identity_matrix =
     (lambda i j. if i = j then &1 else &0):real^2^2 in
   let matsin =
     \matpow A.
       (lambda i j.
          suminf
            (\n:num.
               (-- &1) pow n / &(FACT (2 * n + 1)) *
               (matpow A (2 * n + 1))$i$j)):real^2^2 in
   let mat1996 =
     (lambda i j.
        if i = 1 then (if j = 1 then &1 else &1996)
        else (if j = 1 then &0 else &1)):real^2^2 in
   let putnam_1996_b4_solution = F in
   !matpow:real^2^2->num->real^2^2.
     (!A:real^2^2.
        matpow A 0 = identity_matrix /\
        (!k:num.
           matpow A (k + 1) = matrix_mul A (matpow A k)))
     ==>
     ((?A:real^2^2. matsin matpow A = mat1996) <=>
      putnam_1996_b4_solution)`;;
