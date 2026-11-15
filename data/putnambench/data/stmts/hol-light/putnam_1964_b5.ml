(*
  Statement-only formalization of PutnamBench artifact putnam_1964_b5:
  convergence of the reciprocal series of the successive least common
  multiples of a strictly increasing sequence of positive integers.
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
  `!a b:num->num.
     ((!m n:num. m < n ==> a m < a n) /\
      (!n:num. 0 < a n)) /\
     (b 0 = a 0 /\
      (!n:num. b (n + 1) = lcm(b n,a (n + 1))))
     ==> summable (\n:num. &1 / &(b n))`;;
