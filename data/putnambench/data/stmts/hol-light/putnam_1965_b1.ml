(*
  Statement-only formalization of PutnamBench artifact putnam_1965_b1:
  convergence to 1/2 of the iterated unit-cube integrals of the squared
  cosine of the normalized coordinate sum. This file contains no proof.
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
  `let integrate_one =
     \(g:real->real) (s:real).
       integral(&0,&1) (\x. g (s + x)) in
   let cube_integral =
     \n:num.
       ITER (n + 1) integrate_one
         (\s. (cos (pi / (&2 * &(n + 1)) * s)) pow 2) (&0) in
   cube_integral tends_num_real (&1 / &2)`;;
