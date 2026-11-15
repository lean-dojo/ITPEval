(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_b3:
  for every integer n greater than 1, the difference between 1/e and
  (1 - 1/n)^n lies strictly between 1/(2ne) and 1/(ne). This file contains
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
  `!n:int.
     (&1:int) < n
     ==>
     let nr = real_of_int n in
     &1 / (&2 * nr * exp (&1))
     < &1 / exp (&1) - (&1 - &1 / nr) pow (num_of_int n) /\
     &1 / exp (&1) - (&1 - &1 / nr) pow (num_of_int n)
     < &1 / (nr * exp (&1))`;;
