(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_a2:
  the geometric-mean inequality for two finite sequences of nonnegative real
  numbers and their pointwise sums. This file contains no proof.
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
  `!n:num. !a b:num->real.
     0 < n /\
     (!i. i IN 0..n-1 ==> &0 <= a i /\ &0 <= b i)
     ==>
     root n (product (0..n-1) a) +
     root n (product (0..n-1) b) <=
     root n (product (0..n-1) (\i. a i + b i))`;;
