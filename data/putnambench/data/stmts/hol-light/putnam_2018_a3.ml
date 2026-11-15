(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_a3
  (putnambench__hol-light__putnam_2018_a3): the greatest possible sum of the
  cosines of three times ten real angles, when the sum of their cosines is
  zero, is 480/49. This file contains no proof.
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
  `let admissible =
     \(x:num->real).
       sum (0..9) (\i:num. cos (x i)) = &0 in
   let objective =
     \(x:num->real).
       sum (0..9) (\i:num. cos (&3 * x i)) in
   let putnam_2018_a3_solution = &480 / &49 in
   (?x:num->real.
      admissible x /\ objective x = putnam_2018_a3_solution) /\
   (!x:num->real.
      admissible x ==> objective x <= putnam_2018_a3_solution)`;;
