(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_a3:
  convergence to 3/7 of the partial products associated with the real sequence
  starting at 5/2 and satisfying a quadratic recurrence. This file contains
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
  `!a:num->real.
     a 0 = &5 / &2 /\
     (!k:num. 1 <= k ==> a k = (a (k - 1)) pow 2 - &2)
     ==>
     (\n:num.
        if n = 0 then &1
        else product (0..n - 1) (\k:num. &1 - &1 / a k))
     tends_num_real (&3 / &7)`;;
