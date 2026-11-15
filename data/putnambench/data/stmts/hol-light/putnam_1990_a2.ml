(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_a2:
  existence of a sequence of differences of cube roots of natural numbers
  converging to the square root of 2. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let rpow =
     \x p:real. if x = &0 then &0 else exp (p * ln x) in
   let numform =
     \x:real.
       ?n m:num.
         x = rpow (&n) (&1 / &3) - rpow (&m) (&1 / &3) in
   let putnam_1990_a2_solution = T in
   ((?s:num->real.
       (!i:num. numform (s i)) /\
       s tends_num_real (sqrt (&2)))
    <=> putnam_1990_a2_solution)`;;
