(*
  Statement-only formalization of PutnamBench artifact putnam_1975_b6:
  strict upper and lower inequalities involving harmonic partial sums and
  real nth roots. This file contains no proof.
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
  `let s = \n:num. sum (1..n) (\i:num. &1 / &i) in
   (!n:num.
      n > 1
      ==> &n * exp ((&1 / &n) * ln (&n + &1)) < &n + s n) /\
   (!n:num.
      n > 2
      ==> (&n - &1) * exp ((-- &1 / (&n - &1)) * ln (&n))
          < &n - s n)`;;
