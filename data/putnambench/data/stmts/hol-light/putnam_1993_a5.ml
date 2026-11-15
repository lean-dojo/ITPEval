(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_a5:
  the sum of three specified definite integrals of a squared rational function
  is rational. This file contains no proof.
*)

let transc_output = open_out "/dev/null";;
let transc_formatter = Format.formatter_of_out_channel transc_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file transc_formatter path);;
let transc_loaded =
  Toploop.use_file transc_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush transc_formatter ();;
close_out transc_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let f =
     \x:real.
       ((x pow 2 - x) / (x pow 3 - &3 * x + &1)) pow 2 in
   ?p q:int.
     ~(q = &0) /\
     integral(--(&100),--(&10)) f +
     integral(&1 / &101,&1 / &11) f +
     integral(&101 / &100,&11 / &10) f =
     real_of_int p / real_of_int q`;;
