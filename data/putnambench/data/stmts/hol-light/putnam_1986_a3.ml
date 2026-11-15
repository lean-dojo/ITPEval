(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_a3:
  evaluation of the infinite series of principal arccotangents at
  n^2 + n + 1 as pi/2. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!cot arccot:real->real.
     cot = (\theta:real. cos theta / sin theta) /\
     (!t:real.
        &0 <= t
        ==> &0 < arccot t /\
            arccot t <= pi / &2 /\
            cot (arccot t) = t)
     ==> (\n:num. arccot ((&n) pow 2 + &n + &1)) sums (pi / &2)`;;
