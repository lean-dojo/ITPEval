(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_b3:
  the real exponential growth rates eventually dominated by every positive
  differentiable function whose derivative is everywhere larger than the
  function itself. This file contains no proof.
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
     \(f:real->real) (x:real). @d. (f diffl d) x in
   {k:real |
      !f:real->real.
        ((!x:real. &0 < f x /\ f x < deriv f x) /\
         (!x:real. f differentiable x))
        ==> ?N:real. !x:real. x > N ==> f x > exp (k * x)} =
   {k:real | k < &1}`;;
