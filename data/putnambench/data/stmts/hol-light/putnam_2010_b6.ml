(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_b6:
  equality of ordinary matrix powers and entrywise powers through exponent
  n+1 implies equality for every positive exponent. This file contains no
  proof.
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
     \(A:I->I->real) (B:I->I->real) i j.
       sum (UNIV:I->bool) (\k:I. A i k * B k j) in
   let identity_matrix =
     \i j:I. if i = j then &1 else &0 in
   let matrix_pow =
     \(A:I->I->real) k.
       ITER k (matrix_mul A) identity_matrix in
   !n:num. !A:I->I->real.
     FINITE (UNIV:I->bool) /\
     CARD (UNIV:I->bool) = n /\
     0 < n
     ==>
     ((!k:num.
         1 <= k /\ k <= n + 1
         ==> matrix_pow A k = (\i j:I. (A i j) pow k))
      ==>
      (!k:num.
         1 <= k
         ==> matrix_pow A k = (\i j:I. (A i j) pow k)))`;;
