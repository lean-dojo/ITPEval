(*
  Statement-only formalization of PutnamBench artifact putnam_1982_a6:
  whether the stated decay and monotonicity conditions force a bijective
  rearrangement of a real series to retain sum 1; the expected answer is
  false. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let positive = {n:num | 1 <= n} in
   let strictly_decreasing_abs =
     \(x:num->real).
       !i j:num.
         i IN positive /\ j IN positive /\ i < j
         ==> abs (x j) < abs (x i) in
   ((!b:num->num.
       !x:num->real.
         BIJ b positive positive /\
         strictly_decreasing_abs x /\
         ((\n:num. abs (&(b n) - &n) * abs (x n)) tends_num_real &0) /\
         ((\n:num. sum (1..n) x) tends_num_real &1)
         ==> ((\n:num. sum (1..n) (\k. x (b k))) tends_num_real &1))
    <=> F)`;;
