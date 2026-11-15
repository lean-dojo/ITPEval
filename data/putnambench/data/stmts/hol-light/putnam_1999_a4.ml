(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_a4:
  the iterated real series with terms m^2 n / (3^m (n 3^m + m 3^n))
  sums to 9/32. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `(\m:num.
      suminf
        (\n:num.
           (&(m + 1) pow 2 * &(n + 1)) /
           (&3 pow (m + 1) *
            (&(n + 1) * &3 pow (m + 1) +
             &(m + 1) * &3 pow (n + 1)))))
   sums (&9 / &32)`;;
