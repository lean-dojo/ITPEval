(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_b6
  (putnambench__hol-light__putnam_2016_b6): evaluation as 1 of the iterated
  alternating real series with inner terms 1 / (k * 2^n + 1). This file
  contains no proof.
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
     \k n:num.
       &1 / (&(k + 1) * (&2 pow n) + &1) in
   ?row_sum:num->real.
     (!k:num. (\n:num. term k n) sums row_sum k) /\
     (\k:num.
        (--(&1)) pow k / &(k + 1) * row_sum k)
     sums &1`;;
