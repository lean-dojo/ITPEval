(*
  Statement-only formalization of PutnamBench artifact putnam_1978_a5:
  the product of sin(a_i) / a_i for a nonempty finite family of reals in
  (0, pi) is bounded by the corresponding value at its arithmetic mean.
  This file contains no proof.
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
  `!n:num. !a:num->real. !mu:real.
     0 < n /\
     (!i:num. i IN (1..n) ==> &0 < a i /\ a i < pi) /\
     mu = sum (1..n) a / &n
     ==> product (1..n) (\i:num. sin (a i) / a i) <=
         (sin mu / mu) pow n`;;
