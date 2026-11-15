(*
  Statement-only formalization of Thousand Theorems corpus artifact Q470877,
  "Stirling's theorem": the factorial-based Stirling sequence tends to the
  square root of pi. This file contains no proof.
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
if not transc_loaded then
  failwith "failed to load Library/transc.ml";;

let Q470877_STIRLING_S_THEOREM =
  `(\n:num.
      &(FACT n) /
      (sqrt(&2 * &n) * (&n / exp(&1)) pow n))
   tends_num_real sqrt pi`;;
