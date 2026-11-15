(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_a5
  (putnambench__hol-light__putnam_2018_a5): a globally nonnegative infinitely
  differentiable real function with prescribed values at 0 and 1 has a
  negative derivative of some positive order. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file analysis_formatter path);;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
let iter_loaded =
  Toploop.use_file analysis_formatter "Library/iter.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;
if not iter_loaded then failwith "failed to load Library/iter.ml";;

let statement =
  `let deriv =
     \(g:real->real) (x:real). @d:real. (g diffl d) x in
   !f:real->real.
     (!n:num. !x:real. (ITER n deriv f) differentiable x) /\
     f (&0) = &0 /\
     f (&1) = &1 /\
     (!x:real. &0 <= f x)
     ==>
     ?n:num. ?x:real.
       0 < n /\ ITER n deriv f x < &0`;;
