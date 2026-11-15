(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_a1:
  the real lines y = a*x + b meeting y = ln(1 + x^2) in exactly one point
  are characterized explicitly by conditions on a and b. This file contains
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
     (?!x:real. a * x + b = ln (&1 + x pow 2)) <=>
     (a = &0 /\ b = &0) \/
     &1 <= abs a \/
     (&0 < abs a /\ abs a < &1 /\
      let rminus = (&1 - sqrt (&1 - a pow 2)) / a in
      let rplus = (&1 + sqrt (&1 - a pow 2)) / a in
      (b < ln (&1 + rminus pow 2) - a * rminus \/
       ln (&1 + rplus pow 2) - a * rplus < b))`;;
