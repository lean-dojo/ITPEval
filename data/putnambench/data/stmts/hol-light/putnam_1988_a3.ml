(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_a3:
  classification of the real exponents for which the series with terms
  ((1/n) / sin(1/n) - 1)^x converges. This file contains no proof.
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
  `let rpow =
     \u x:real. if u = &0 then &0 else exp (x * ln u) in
   {x:real |
      ?L:real.
        (\m:num.
           sum (1..m)
             (\n:num.
                rpow ((&1 / &n) / sin (&1 / &n) - &1) x))
        tends_num_real L} =
   {x:real | &1 / &2 < x}`;;
