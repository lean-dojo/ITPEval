(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_b5
  (putnambench__hol-light__putnam_2020_b5): a nonvanishing polynomial
  expression in four unit complex numbers, none equal to one. This file
  contains no proof.
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
  `!z1 z2 z3 z4:complex.
     norm z1 = &1 /\
     norm z2 = &1 /\
     norm z3 = &1 /\
     norm z4 = &1 /\
     ~(z1 = Cx(&1)) /\
     ~(z2 = Cx(&1)) /\
     ~(z3 = Cx(&1)) /\
     ~(z4 = Cx(&1))
     ==>
     ~(Cx(&3) - z1 - z2 - z3 - z4 + z1 * z2 * z3 * z4 =
       Cx(&0))`;;
