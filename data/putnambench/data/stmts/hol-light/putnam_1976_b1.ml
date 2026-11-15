(*
  Statement-only formalization of PutnamBench artifact putnam_1976_b1:
  the normalized sum of the differences floor(2n/k) - 2 floor(n/k)
  converges to ln(4) - 1. This file contains no proof.
*)

let library_output = open_out "/dev/null";;
let library_formatter = Format.formatter_of_out_channel library_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file library_formatter path);;
let floor_loaded =
  Toploop.use_file library_formatter "Library/floor.ml";;
let transc_loaded =
  Toploop.use_file library_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush library_formatter ();;
close_out library_output;;
if not floor_loaded then failwith "failed to load Library/floor.ml";;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let putnam_1976_b1_solution = (&4:real,&1:real) in
   (\n:num.
      (&1 / &n) *
      sum (1..n)
        (\k:num.
           floor ((&2 * &n) / &k) -
           &2 * floor (&n / &k)))
   tends_num_real
   (ln (FST putnam_1976_b1_solution) -
    SND putnam_1976_b1_solution)`;;
