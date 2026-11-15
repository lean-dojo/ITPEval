(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_b2:
  evaluation as -1 of the limit of n! F_n(1) / ln n for the sequence of
  functions obtained by iterated integration starting from ln. This file
  contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `!f:num->real->real.
     (!x:real. f 0 x = ln x) /\
     (!n:num. !x:real.
        &0 < x
        ==> f (n + 1) x = integral(&0,x) (f n))
     ==>
     (\n:num. &(FACT n) * f n (&1) / ln (&n))
     tends_num_real (-- &1)`;;
