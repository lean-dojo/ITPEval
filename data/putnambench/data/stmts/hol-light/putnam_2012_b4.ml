(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_b4:
  finite convergence of a_n - ln(n) for the real sequence starting at one
  and satisfying a_(n+1) = a_n + exp(-a_n). This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let putnam_2012_b4_solution = T in
   !a:num->real.
     (a 0 = &1 /\
      (!n:num. a (n + 1) = a n + exp (--(a n))))
     ==>
     ((?L:real. (\n:num. a n - ln (&n)) tends_num_real L) <=>
      putnam_2012_b4_solution)`;;
