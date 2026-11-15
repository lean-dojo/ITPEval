(*
  Statement-only formalization of PutnamBench artifact putnam_1975_a2:
  characterization of the real coefficients for which every complex root of
  a monic quadratic lies strictly inside the unit disk. This file contains no
  proof.
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
  `!b c:real.
     (!z:complex.
        z pow 2 + Cx b * z + Cx c = Cx(&0)
        ==> norm z < &1) <=>
     c < &1 /\ c - b > -- &1 /\ c + b > -- &1`;;
