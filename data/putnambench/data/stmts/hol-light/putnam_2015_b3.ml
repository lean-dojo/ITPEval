(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_b3:
  classification of real 2 by 2 arithmetic-progression matrices having a
  higher natural power whose entries again form an arithmetic progression.
  This file contains no proof.
*)

let iter_output = open_out "/dev/null";;
let iter_formatter = Format.formatter_of_out_channel iter_output;;
let iter_loaded =
  Toploop.use_file iter_formatter "Library/iter.ml";;
Format.pp_print_flush iter_formatter ();;
close_out iter_output;;
if not iter_loaded then failwith "failed to load Library/iter.ml";;

let statement =
  `let matrix_mul =
     \A B:real^2^2.
       (lambda i j. sum (1..2) (\r. A$i$r * B$r$j)):real^2^2 in
   let identity_matrix =
     (lambda i j. if i = j then &1 else &0):real^2^2 in
   let matrix_pow =
     \A:real^2^2. \k:num.
       ITER k (matrix_mul A) identity_matrix in
   let in_arithmetic_progression =
     \A:real^2^2.
       A$1$2 - A$1$1 = A$2$1 - A$1$2 /\
       A$2$1 - A$1$2 = A$2$2 - A$2$1 in
   !M:real^2^2.
     (in_arithmetic_progression M /\
      (?k:num.
         1 < k /\
         in_arithmetic_progression (matrix_pow M k)))
     <=>
     ((?alpha:real.
         M$1$1 = alpha /\
         M$1$2 = alpha /\
         M$2$1 = alpha /\
         M$2$2 = alpha) \/
      (?beta:real.
         M$1$1 = -- &3 * beta /\
         M$1$2 = -- &1 * beta /\
         M$2$1 = &1 * beta /\
         M$2$2 = &3 * beta))`;;
