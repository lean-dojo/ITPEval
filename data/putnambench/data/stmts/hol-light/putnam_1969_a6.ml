(*
  Statement-only formalization of PutnamBench artifact putnam_1969_a6:
  convergence of a real sequence whose fixed linear combination with its
  preceding term converges. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!x y:num->real.
     ((!n:num. 2 <= n ==> y n = x (n - 1) + &2 * x n) /\
      (?c:real. y tends_num_real c))
     ==> ?c:real. x tends_num_real c`;;
