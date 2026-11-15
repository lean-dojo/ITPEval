(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_a2:
  evaluation of an integral involving the 1992nd Taylor coefficient of
  (1 + x)^alpha and a finite harmonic-type sum. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file analysis_formatter path);;
let transc_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
let iter_loaded =
  Toploop.use_file analysis_formatter "Library/iter.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;
if not iter_loaded then failwith "failed to load Library/iter.ml";;

let statement =
  `let deriv =
     \(f:real->real) (x:real). @d. (f diffl d) x in
   let C =
     \alpha:real.
       (ITER 1992 deriv
          (\x:real. exp (alpha * ln (&1 + x)))) (&0) /
       &(FACT 1992) in
   integral(&0,&1)
     (\y. C (--y - &1) *
          sum (1..1992) (\k:num. &1 / (y + &k))) =
   &1992`;;
