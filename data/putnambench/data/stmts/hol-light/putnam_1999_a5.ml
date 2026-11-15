(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_a5:
  existence of a uniform constant bounding a degree-1999 real polynomial's
  value at zero by its absolute-value integral on [-1,1]. This file contains
  no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `?C:real.
     !a:num->real.
       ~(a 1999 = &0)
       ==>
       abs (sum (0..1999) (\i:num. a i * (&0) pow i)) <=
       C *
       integral(-- &1,&1)
         (\x:real.
            abs (sum (0..1999) (\i:num. a i * x pow i)))`;;
