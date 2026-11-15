(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_b5
  (putnambench__hol-light__putnam_2021_b5): positive powers of an integer
  square matrix with every nonempty principal minor odd have the same
  property. This file contains no proof.
*)

let libraries_output = open_out "/dev/null";;
let libraries_formatter =
  Format.formatter_of_out_channel libraries_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file libraries_formatter path);;
let iter_loaded =
  Toploop.use_file libraries_formatter "Library/iter.ml";;
let determinants_loaded =
  Toploop.use_file libraries_formatter "Multivariate/determinants.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush libraries_formatter ();;
close_out libraries_output;;
if not (iter_loaded && determinants_loaded) then
  failwith "failed to load HOL Light iteration and determinant libraries";;

let statement =
  `let integer_matrix =
     \(A:real^N^N).
       !i j:num.
         i IN 1..dimindex(:N) /\ j IN 1..dimindex(:N)
         ==> integer (A$i$j) in
   let odd_integer =
     \x:real.
       ?m:num. x = &(2 * m + 1) \/ x = --(&(2 * m + 1)) in
   let principal_extension =
     \(A:real^N^N) (S:num->bool).
       (lambda i j.
          if i IN S /\ j IN S then A$i$j
          else if i = j then &1 else &0):real^N^N in
   let very_odd =
     \(A:real^N^N).
       integer_matrix A /\
       !S:num->bool.
         S SUBSET (1..dimindex(:N)) /\ ~(S = {})
         ==> odd_integer (det (principal_extension A S)) in
   let matrix_power =
     \(A:real^N^N) (k:num).
       ITER k (\X:real^N^N. X ** A) (mat 1) in
   !A:real^N^N.
     very_odd A
     ==> !k:num. 1 <= k ==> very_odd (matrix_power A k)`;;
