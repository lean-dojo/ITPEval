(*
  Statement-only formalization of PutnamBench artifact putnam_1981_b5:
  rationality of the exponential of the infinite series formed from binary
  digit sums. This file contains no proof.
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
  `let B =
     \n:num. CARD {k:num | ODD (n DIV (2 EXP k))} in
   let S =
     suminf
       (\n:num.
          &(B (n + 1)) / (&(n + 1) * &(n + 2))) in
   ?p q:int.
     ~(q = (&0:int)) /\
     exp S = real_of_int p / real_of_int q`;;
