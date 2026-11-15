(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_a3:
  every complex root of the specified degree-ten polynomial has modulus one.
  This file contains no proof.
*)

let complex_output = open_out "/dev/null";;
let complex_formatter = Format.formatter_of_out_channel complex_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file complex_formatter path);;
let complex_loaded =
  Toploop.use_file complex_formatter "Complex/complexnumbers.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush complex_formatter ();;
close_out complex_output;;
if not complex_loaded then
  failwith "failed to load Complex/complexnumbers.ml";;

let statement =
  `!z:complex.
     Cx(&11) * z pow 10 +
     Cx(&10) * ii * z pow 9 +
     Cx(&10) * ii * z -
     Cx(&11) = Cx(&0)
     ==> norm z = &1`;;
