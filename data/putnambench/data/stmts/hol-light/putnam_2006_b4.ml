(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_b4:
  the maximum number of Boolean-cube vertices lying in a k-dimensional real
  linear subspace is 2^k. This file contains no proof.
*)

let vectors_output = open_out "/dev/null";;
let vectors_formatter = Format.formatter_of_out_channel vectors_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file vectors_formatter path);;
let vectors_loaded =
  Toploop.use_file vectors_formatter "Multivariate/vectors.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush vectors_formatter ();;
close_out vectors_output;;
if not vectors_loaded then failwith "failed to load Multivariate/vectors.ml";;

let statement =
  `let Z =
     {x:real^N |
        !i:num.
          1 <= i /\ i <= dimindex(:N)
          ==> x$i = &0 \/ x$i = &1} in
   !n k:num.
     dimindex(:N) = n /\
     0 < n /\
     k <= n
     ==>
     (?V:real^N->bool.
        subspace V /\
        dim V = k /\
        CARD (Z INTER V) = 2 EXP k) /\
     (!V:real^N->bool.
        subspace V /\ dim V = k
        ==> CARD (Z INTER V) <= 2 EXP k)`;;
