(*
  Statement-only formalization of PutnamBench artifact putnam_1982_a2:
  convergence of the series whose terms use sums of real powers evaluated at
  logarithms with varying bases. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let rpow =
     \x p:real. if x = &0 then &0 else exp (p * ln x) in
   let logb =
     \b x:real. ln x / ln b in
   let B =
     \n x. sum (1..n) (\k. rpow (&k) x) in
   let f =
     \n. B n (logb (&n) (&2)) /
         ((&n * logb (&2) (&n)) pow 2) in
   ((?L:real. (\N. sum (2..N) f) tends_num_real L) <=> T)`;;
