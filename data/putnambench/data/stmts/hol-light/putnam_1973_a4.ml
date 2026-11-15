(*
  Statement-only formalization of PutnamBench artifact putnam_1973_a4:
  the real function 2^x - 1 - x^2 has exactly three zeros. This file contains
  no proof.
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
  `let f = \x:real. exp (x * ln (&2)) - &1 - x pow 2 in
   {x:real | f x = &0} HAS_SIZE 3`;;
