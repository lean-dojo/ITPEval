(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_b5:
  the rank is 2n for the specified (2n+1) by (2n+1) real skew-symmetric
  matrix with prescribed entries below the diagonal. This file contains no
  proof.
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
  `let putnam_1988_b5_solution = \n:num. 2 * n in
   !n:num. !Mn:real^N^N.
     0 < n /\
     dimindex(:N) = 2 * n + 1 /\
     (!i j:num.
        1 <= i /\ i <= 2 * n + 1 /\
        1 <= j /\ j <= 2 * n + 1
        ==> Mn$i$j = --(Mn$j$i)) /\
     (!i j:num.
        1 <= i /\ i <= 2 * n + 1 /\
        1 <= j /\ j <= 2 * n + 1 /\
        1 <= i - j /\ i - j <= n
        ==> Mn$i$j = &1) /\
     (!i j:num.
        1 <= i /\ i <= 2 * n + 1 /\
        1 <= j /\ j <= 2 * n + 1 /\
        n < i - j
        ==> Mn$i$j = -- &1)
     ==> rank Mn = putnam_1988_b5_solution n`;;
