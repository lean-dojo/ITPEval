(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_a2:
  evaluation of a double integral over a positive rectangle whose integrand
  is the exponential of the maximum of two scaled squares. This file contains
  no proof.
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
  `!a b:real.
     &0 < a /\ &0 < b
     ==>
     integral(&0,a)
       (\x. integral(&0,b)
              (\y. exp (max (b pow 2 * x pow 2)
                            (a pow 2 * y pow 2)))) =
     (exp (a pow 2 * b pow 2) - &1) / (a * b)`;;
