(*
  Statement-only formalization of PutnamBench artifact putnam_1966_b3:
  convergence of the reciprocal series of a positive real sequence implies
  convergence of the series whose nth term is n squared times p(n), divided
  by the square of the prefix sum through n. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!p:num->real.
     (!n:num. &0 < p n) /\
     (?r:real.
        (\m:num. sum (1..m) (\n:num. &1 / p n)) tends_num_real r)
     ==> ?r:real.
           (\m:num.
              sum (1..m)
                (\n:num.
                   p n * (&n) pow 2 /
                   (sum (1..n) p) pow 2))
           tends_num_real r`;;
