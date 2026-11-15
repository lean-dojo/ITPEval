(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_a3:
  coefficients of the power series for 1 / (1 - 2x - x^2) satisfy that each
  sum of two consecutive coefficient squares is another coefficient. This file
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
  `!a:num->real.
     (?e:real.
        &0 < e /\
        !x:real.
          abs x < e
          ==> (\n:num. a n * x pow n) sums
              (&1 / (&1 - &2 * x - x pow 2)))
     ==> !n:num.
           ?m:num. (a n) pow 2 + (a (n + 1)) pow 2 = a m`;;
