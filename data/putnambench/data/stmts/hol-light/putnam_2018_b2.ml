(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_b2:
  the polynomial with coefficients n,n-1,...,1 has no complex zero in the
  closed unit disk. This file contains no proof.
*)

let complex_output = open_out "/dev/null";;
let complex_formatter = Format.formatter_of_out_channel complex_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file complex_formatter path);;
let complex_loaded =
  Toploop.use_file complex_formatter "Complex/complexnumbers.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush complex_formatter ();;
close_out complex_output;;
if not complex_loaded then
  failwith "failed to load Complex/complexnumbers.ml";;

let statement =
  `let f =
     \n:num. \z:complex.
       iterate ((+):complex->complex->complex)
         (0..n - 1) (\i. Cx(&(n - i)) * z pow i) in
   !n:num. !z:complex.
     0 < n /\ norm z <= &1
     ==> ~(f n z = Cx(&0))`;;
