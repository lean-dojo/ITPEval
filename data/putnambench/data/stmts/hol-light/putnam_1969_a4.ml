(*
  Statement-only formalization of PutnamBench artifact putnam_1969_a4:
  convergence of the alternating series with terms n^(-n) to the definite
  integral of x^x on the unit interval. This file contains no proof.
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
  `(\n:num.
      sum (1..n)
        (\i. (-- &1) pow (i + 1) / (&i pow i)))
   tends_num_real
   integral(&0,&1) (\x. exp (x * ln x))`;;
