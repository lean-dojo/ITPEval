(*
  Statement-only formalization of PutnamBench artifact putnam_1978_b2:
  evaluation of a positive-integer double series with rational summands as
  seven fourths. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let term =
     \i j:num.
       &1 /
       (&(i + 1) pow 2 * &(j + 1) +
        &2 * &(i + 1) * &(j + 1) +
        &(i + 1) * &(j + 1) pow 2) in
   ?row_sum:num->real.
     (!i:num. (\j:num. term i j) sums row_sum i) /\
     (\i:num. row_sum i) sums (&7 / &4)`;;
