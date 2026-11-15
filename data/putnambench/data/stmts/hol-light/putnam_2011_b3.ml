(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_b3:
  nonvanishing and continuity of g at zero, together with differentiability
  there of f*g and f/g, imply differentiability of f. This file contains no
  proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let putnam_2011_b3_solution = T in
   ((!f g:real->real.
       ~(g (&0) = &0) /\
       g contl (&0) /\
       (\x:real. f x * g x) differentiable (&0) /\
       (\x:real. f x / g x) differentiable (&0)
       ==> f differentiable (&0))
    <=> putnam_2011_b3_solution)`;;
