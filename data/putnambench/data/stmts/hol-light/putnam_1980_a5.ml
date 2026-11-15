(*
  Statement-only formalization of PutnamBench artifact putnam_1980_a5:
  finiteness of the common real zeros of the sine- and cosine-weighted
  integrals of a nonconstant real polynomial. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let interval_integral =
     \(f:real->real) (x:real).
       if &0 <= x
       then integral(&0,x) f
       else --(integral(x,&0) f) in
   !P:real->real.
     polynomial_function P /\
     ~(?c:real. !t:real. P t = c)
     ==> FINITE
           {x:real |
              interval_integral (\t. P t * sin t) x = &0 /\
              interval_integral (\t. P t * cos t) x = &0}`;;
