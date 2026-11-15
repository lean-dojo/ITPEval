(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_b2:
  the product of the first n positive odd integers lies between the specified
  real-power bounds involving e. This file contains no proof.
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
     \x p:real. if x = &0 then &0 else exp (p * ln x) in
   !n:num.
     0 < n
     ==>
     let prododd =
       product (1..n) (\i:num. &(2 * i - 1)) in
     rpow ((&(2 * n - 1)) / exp (&1)) ((&(2 * n - 1)) / &2)
     < prododd /\
     prododd
     < rpow ((&(2 * n + 1)) / exp (&1)) ((&(2 * n + 1)) / &2)`;;
