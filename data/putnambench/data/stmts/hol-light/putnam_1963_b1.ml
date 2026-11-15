(*
  Statement-only formalization of PutnamBench artifact putnam_1963_b1:
  the integer parameter for which x^2 - x + a divides x^13 + x + 90.
  This file contains no proof.
*)

let poly_output = open_out "/dev/null";;
let poly_formatter = Format.formatter_of_out_channel poly_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file poly_formatter path);;
let poly_loaded =
  Toploop.use_file poly_formatter "Library/poly.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush poly_formatter ();;
close_out poly_output;;
if not poly_loaded then failwith "failed to load Library/poly.ml";;

let statement =
  `!a:int.
     poly_divides
       [real_of_int a; -- &1; &1]
       [&90; &1; &0; &0; &0; &0; &0;
        &0; &0; &0; &0; &0; &0; &1]
     <=> a = (&2:int)`;;
