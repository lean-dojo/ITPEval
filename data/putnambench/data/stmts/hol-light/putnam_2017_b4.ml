(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_b4
  (putnambench__hol-light__putnam_2017_b4): evaluation of an infinite real
  series of logarithmic terms as the square of ln 2. This file contains no
  proof.
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
  `(\k:num.
      &3 * ln (&(4 * k + 2)) / &(4 * k + 2) -
      ln (&(4 * k + 3)) / &(4 * k + 3) -
      ln (&(4 * k + 4)) / &(4 * k + 4) -
      ln (&(4 * k + 5)) / &(4 * k + 5))
   sums ((ln (&2)) pow 2)`;;
