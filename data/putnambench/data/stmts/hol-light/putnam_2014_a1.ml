(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_a1:
  reduced numerators of the nonzero Taylor coefficients at zero of
  (1 - x + x^2) times the real exponential. This file contains no proof.
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
     \x:real. (&1 - x + x pow 2) * exp x in
   !D:num->real->real.
     D 0 = f /\
     (!k:num. !x:real. (D k diffl D (SUC k) x) x)
     ==>
     !n:num.
       ~(D n (&0) / &(FACT n) = &0)
       ==>
       ?a:int b:num.
         0 < b /\
         coprime (num_of_int (abs a),b) /\
         D n (&0) / &(FACT n) = real_of_int a / &b /\
         (a = (&1:int) \/ prime (num_of_int (abs a)))`;;
