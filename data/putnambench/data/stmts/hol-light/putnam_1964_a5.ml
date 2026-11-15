(*
  Statement-only formalization of PutnamBench artifact putnam_1964_a5:
  a universal constant bounds the series of prefix-sum ratios for every
  positive real sequence with summable reciprocals. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `?k:real.
     !a:num->real.
       (!n:num. &0 < a n) /\
       summable (\n:num. &1 / a n)
       ==> ?L1 L2:real.
             (\n:num. &(n + 1) / sum (0..n) a) sums L1 /\
             (\n:num. &1 / a n) sums L2 /\
             L1 <= k * L2`;;
