(*
  Statement-only formalization of Thousand Theorems corpus artifact Q810431
  (thousand-theorems__hol-light__Q810431), "Basel problem": the real series
  with nth term 1 / n^2 sums to pi^2 / 6, with the zero-indexed term interpreted
  by totalized real division. This file contains no proof.
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

let Q810431_BASEL_PROBLEM =
  `(\n:num. &1 / (&n pow 2)) sums (pi pow 2 / &6)`;;
