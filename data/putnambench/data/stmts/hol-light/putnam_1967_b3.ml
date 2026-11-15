(*
  Statement-only formalization of PutnamBench artifact putnam_1967_b3:
  the limit of the integral of f(x)g(nx) for continuous period-one real
  functions is the product of their integrals. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!f g:real->real.
     (!x. f contl x) /\
     (!x. g contl x) /\
     (!x. f (x + &1) = f x) /\
     (!x. g (x + &1) = g x)
     ==>
     (\n:num.
        integral(&0,&1) (\x. f x * g (&n * x)))
     tends_num_real
     (integral(&0,&1) f * integral(&0,&1) g)`;;
