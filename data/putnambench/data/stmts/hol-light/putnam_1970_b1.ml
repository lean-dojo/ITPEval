(*
  Statement-only formalization of PutnamBench artifact putnam_1970_b1:
  evaluation of a normalized finite product with real nth-root factors as
  n tends to infinity. This file contains no proof.
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
  `let putnam_1970_b1_solution =
     exp (&2 * ln (&5) - &4 + &2 * atn (&2)) in
   (\n:num.
      (&1 / (&n pow 4)) *
      product (1..2*n)
        (\i. exp ((&1 / &n) * ln ((&n pow 2) + (&i pow 2)))))
   tends_num_real
   putnam_1970_b1_solution`;;
