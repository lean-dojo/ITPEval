(*
  Statement-only formalization of PutnamBench artifact putnam_1969_b3:
  evaluation of the first term of a real sequence whose adjacent products
  equal their indices and whose consecutive-term ratios converge to one.
  This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!t:num->real.
     (!n:num. 1 <= n ==> t n * t (n + 1) = &n) /\
     ((\n:num. t n / t (n + 1)) tends_num_real &1)
     ==> pi * (t 1) pow 2 = &2`;;
