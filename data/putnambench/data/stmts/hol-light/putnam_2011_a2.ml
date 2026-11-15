(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_a2:
  convergence to 3/2 of the reciprocal prefix-product series for positive
  real sequences satisfying the stated recurrence and boundedness condition.
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
  `!a b:num->real.
     (!n:num. &0 < a n /\ &0 < b n) /\
     a 0 = &1 /\ b 0 = &1 /\
     (!n:num. 1 <= n ==> b n = b (n - 1) * a n - &2) /\
     (?B:real. !n:num. abs (b n) <= B)
     ==>
     (\n:num.
        if n = 0 then &0
        else sum (0..n - 1)
          (\i:num. &1 / product (0..i) (\j:num. a j)))
     tends_num_real (&3 / &2)`;;
