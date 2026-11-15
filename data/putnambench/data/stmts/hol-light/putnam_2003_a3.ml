(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_a3:
  the minimum absolute value of the given sum of sine, cosine, tangent, and
  their reciprocals is 2 * sqrt 2 - 1. This file contains no proof.
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
  `let f =
     \x:real.
       abs
         (sin x + cos x + tan x +
          &1 / tan x + &1 / cos x + &1 / sin x) in
   (?x:real. f x = &2 * sqrt (&2) - &1) /\
   (!x:real. &2 * sqrt (&2) - &1 <= f x)`;;
