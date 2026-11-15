(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_b5:
  nonexistence of a strictly increasing differentiable real function whose
  derivative at each point equals its value at its own value. This file
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
  `let deriv =
     \(f:real->real) (x:real). @d:real. (f diffl d) x in
   ((?f:real->real.
       (!x y:real. x < y ==> f x < f y) /\
       (!x:real. f differentiable x) /\
       (!x:real. deriv f x = f (f x)))
    <=> F)`;;
