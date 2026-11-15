(*
  Statement-only formalization of PutnamBench artifact putnam_1966_a6:
  convergence to 3 of the first terms of finite nested-radical approximants
  defined by a diagonal boundary value and a square-root recurrence. This file
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
  `!a:num->num->real.
     (!n:num.
        1 <= n
        ==> a n n = &n /\
            (!m:num.
               1 <= m /\ m < n
               ==> a n m = &m * sqrt (&1 + a n (m + 1))))
     ==> (\n:num. a n 1) tends_num_real &3`;;
