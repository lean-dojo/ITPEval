(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_a1:
  the horizontal line y = 4/9 cuts the cubic y = 2x - 3x^3 so that the two
  specified first-quadrant areas are equal. This file contains no proof.
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
  `let putnam_1993_a1_solution = &4 / &9 in
   &0 < putnam_1993_a1_solution /\
   putnam_1993_a1_solution < &4 * sqrt (&2) / &9 /\
   integral(&0,sqrt (&2) / &3)
     (\x:real.
        max
          (putnam_1993_a1_solution -
           (&2 * x - &3 * x pow 3))
          (&0)) =
   integral(&0,sqrt (&6) / &3)
     (\x:real.
        max
          ((&2 * x - &3 * x pow 3) -
           putnam_1993_a1_solution)
          (&0))`;;
