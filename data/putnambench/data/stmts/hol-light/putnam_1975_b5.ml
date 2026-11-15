(*
  Statement-only formalization of PutnamBench artifact putnam_1975_b5:
  the exponential generating series for functions recursively obtained by
  multiplying each derivative by the variable. This file contains no proof.
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
  `let deriv =
     \(g:real->real) (x:real). @d:real. (g diffl d) x in
   !f:num->real->real.
     (!x:real. f 0 x = exp x) /\
     (!n:num. !x:real. f (n + 1) x = x * deriv (f n) x)
     ==> (\n:num. f n (&1) / &(FACT n)) sums exp (exp (&1))`;;
