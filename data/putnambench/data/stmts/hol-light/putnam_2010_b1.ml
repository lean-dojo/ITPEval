(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_b1:
  no infinite real sequence has m-th power series summing to m for every
  positive integer m. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let putnam_2010_b1_solution = F in
   ((?a:num->real.
       !m:num.
         0 < m
         ==> (\i:num. (a i) pow m) sums &m) <=>
    putnam_2010_b1_solution)`;;
