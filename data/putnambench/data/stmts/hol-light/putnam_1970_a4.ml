(*
  Statement-only formalization of PutnamBench artifact putnam_1970_a4:
  a real sequence whose two-step differences tend to zero has its one-step
  differences divided by the index tend to zero. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!x:num->real.
     ((\n:num. x n - x (n - 2)) tends_num_real &0)
     ==> (\n:num. (x n - x (n - 1)) / &n) tends_num_real &0`;;
