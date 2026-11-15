(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_a5:
  evaluation of the integral of ln(x + 1) divided by x squared plus 1 on the
  real unit interval. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `integral(&0,&1)
     (\x:real. ln (x + &1) / (x pow 2 + &1)) =
   pi * ln (&2) / &8`;;
