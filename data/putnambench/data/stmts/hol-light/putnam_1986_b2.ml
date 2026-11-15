(*
  Statement-only formalization of PutnamBench artifact putnam_1986_b2:
  classification of all complex difference triples arising from the given
  symmetric system of quadratic equations. This file contains no proof.
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
  `let putnam_1986_b2_solution =
     \t:complex#complex#complex.
       t = (Cx(&0),Cx(&0),Cx(&0)) \/
       t = (Cx(&0),--(Cx(&1)),Cx(&1)) \/
       t = (Cx(&1),Cx(&0),--(Cx(&1))) \/
       t = (--(Cx(&1)),Cx(&1),Cx(&0)) in
   !t:complex#complex#complex.
     putnam_1986_b2_solution t <=>
     ?x y z:complex.
       t = (x - y,y - z,z - x) /\
       x * (x - Cx(&1)) + Cx(&2) * y * z =
       y * (y - Cx(&1)) + Cx(&2) * z * x /\
       y * (y - Cx(&1)) + Cx(&2) * z * x =
       z * (z - Cx(&1)) + Cx(&2) * x * y`;;
