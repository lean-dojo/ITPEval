(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_b1:
  the real sequence starting at one with logarithmic-exponential recurrence
  has convergent infinite series with sum exp(1) - 1. This file contains no
  proof.
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
  `!x:num->real.
     x 0 = &1 /\
     (!n:num. x (n + 1) = ln (exp (x n) - x n))
     ==> x sums (exp (&1) - &1)`;;
