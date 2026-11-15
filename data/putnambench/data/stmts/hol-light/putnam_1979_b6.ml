(*
  Statement-only formalization of PutnamBench artifact putnam_1979_b6:
  the real part of the principal square root of a finite sum of squares of
  complex numbers is bounded by the sum of their absolute real parts. This
  file contains no proof.
*)

let complex_output = open_out "/dev/null";;
let complex_formatter = Format.formatter_of_out_channel complex_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file complex_formatter path);;
let complex_loaded =
  Toploop.use_file complex_formatter "Complex/complex_transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush complex_formatter ();;
close_out complex_output;;
if not complex_loaded then
  failwith "failed to load Complex/complex_transc.ml";;

let statement =
  `!n:num. !z:num->complex.
     abs
       (Re
         (csqrt
           (iterate ((+):complex->complex->complex)
             (1..n) (\i. (z i) pow 2)))) <=
     sum (1..n) (\i. abs (Re (z i)))`;;
