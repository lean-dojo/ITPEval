(*
  Statement-only formalization of PutnamBench artifact putnam_1964_b1:
  a positive integer sequence with convergent reciprocal series has a
  counting function for terms at most n that is sublinear. This file contains
  no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!a b:num->num.
     (!n:num. 0 < a n) /\
     summable (\n:num. &1 / &(a n)) /\
     (!n:num. b n = CARD {k:num | a k <= n})
     ==> (\n:num. &(b n) / &n) tends_num_real &0`;;
