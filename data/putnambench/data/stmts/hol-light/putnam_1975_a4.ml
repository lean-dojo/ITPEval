(*
  Statement-only formalization of PutnamBench artifact putnam_1975_a4:
  the explicit odd-power integer polynomial expression for the reciprocal of
  one minus a specified complex root of unity. This file contains no proof.
*)

let complex_transc_output = open_out "/dev/null";;
let complex_transc_formatter =
  Format.formatter_of_out_channel complex_transc_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file complex_transc_formatter path);;
let complex_transc_loaded =
  Toploop.use_file complex_transc_formatter "Complex/complex_transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush complex_transc_formatter ();;
close_out complex_transc_output;;
if not complex_transc_loaded then
  failwith "failed to load Complex/complex_transc.ml";;

let statement =
  `let solution =
     \m z.
       iterate ((+):complex->complex->complex)
         (0..((m - 1) DIV 2) - 1)
         (\j. z pow (2 * j + 1)) in
   !m:num theta:complex.
     ODD m /\ 1 < m /\
     theta = cexp (Cx(&2 * pi) * ii / Cx(&(2 * m)))
     ==>
     inv (Cx(&1) - theta) = solution m theta`;;
