(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_b1:
  evaluation as 1 of a definite integral involving square roots of logarithms.
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
  `integral(&2,&4)
     (\x:real.
        sqrt (ln (&9 - x)) /
        (sqrt (ln (&9 - x)) + sqrt (ln (x + &3)))) =
   &1`;;
