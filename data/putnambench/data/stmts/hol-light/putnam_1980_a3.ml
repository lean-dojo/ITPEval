(*
  Statement-only formalization of PutnamBench artifact putnam_1980_a3:
  evaluation of the integral from 0 to pi/2 of the reciprocal of one plus
  tan(x) raised to the square root of 2. This file contains no proof.
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
   integral(&0,pi / &2)
     (\x:real. &1 / (&1 + rpow (tan x) (sqrt (&2)))) =
   pi / &4`;;
