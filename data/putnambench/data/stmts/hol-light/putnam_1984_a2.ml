(*
  Statement-only formalization of PutnamBench artifact putnam_1984_a2:
  the infinite real series with kth term
  6^k / ((3^(k+1) - 2^(k+1)) * (3^k - 2^k)), starting at k = 1,
  has sum 2. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `(\n:num.
      (&6 pow (n + 1)) /
      (((&3 pow (n + 2)) - (&2 pow (n + 2))) *
       ((&3 pow (n + 1)) - (&2 pow (n + 1)))))
   sums (&2)`;;
