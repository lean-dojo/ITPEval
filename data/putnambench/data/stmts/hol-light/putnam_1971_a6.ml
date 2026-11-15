(*
  Statement-only formalization of PutnamBench artifact putnam_1971_a6:
  a real exponent for which every positive integer raised to that exponent is
  an integer must be a nonnegative integer. This file contains no proof.
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
  `!c:real.
     (!n:int.
        (&0:int) < n
        ==> ?m:int.
              exp (c * ln (real_of_int n)) = real_of_int m)
     ==> ?m:int.
           (&0:int) <= m /\ c = real_of_int m`;;
