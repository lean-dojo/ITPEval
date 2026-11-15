(*
  Statement-only formalization of PutnamBench artifact putnam_1978_b5:
  the degree-four real polynomial maximizing its leading coefficient while
  mapping the interval [-1,1] into [0,1]. This file contains no proof.
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
  `let solution:real list = [&1; &0; -- &4; &0; &4] in
   let admissible =
     \p:real list.
       degree p = 4 /\
       (!x:real.
          -- &1 <= x /\ x <= &1
          ==> &0 <= poly p x /\ poly p x <= &1) in
   admissible solution /\
   (!p:real list.
      admissible p
      ==> EL 4 (normalize p) <= EL 4 (normalize solution))`;;
