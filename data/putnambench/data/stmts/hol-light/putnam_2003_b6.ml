(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_b6:
  an integral inequality for the absolute value of the sum of two values of
  a continuous real function on the unit square. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!f:real->real.
     (!x:real. f contl x)
     ==>
     integral(&0,&1)
       (\x:real.
          integral(&0,&1)
            (\y:real. abs (f x + f y))) >=
     integral(&0,&1) (\x:real. abs (f x))`;;
