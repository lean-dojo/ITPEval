(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_a1:
  the possible sums of squares of a positive real sequence with prescribed
  positive total are exactly the reals strictly between zero and its square.
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
  `!A:real.
     &0 < A
     ==> !S:real.
           ((?x:num->real.
               (!j:num. &0 < x j) /\
               x sums A /\
               (\j:num. (x j) pow 2) sums S) <=>
            &0 < S /\ S < A pow 2)`;;
