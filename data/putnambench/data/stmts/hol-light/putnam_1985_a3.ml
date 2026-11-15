(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_a3:
  the diagonal limit of real sequences defined by a quadratic recurrence
  from the initial values d / 2^m. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `!d:real a:num->num->real.
     (!m:num. a m 0 = d / (&2 pow m)) /\
     (!m j:num.
        a m (j + 1) = (a m j) pow 2 + &2 * a m j)
     ==> (\n:num. a n n) tends_num_real (exp d - &1)`;;
