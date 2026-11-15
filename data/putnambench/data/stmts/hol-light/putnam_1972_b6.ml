(*
  Statement-only formalization of PutnamBench artifact putnam_1972_b6:
  a polynomial with constant term one and strictly increasing positive
  integer exponents has no zero in the open disk of radius
  (sqrt 5 - 1) / 2. This file contains no proof.
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
  `!k:num n:num->num zpoly:complex->complex.
     1 <= k /\
     (!i:num. i IN 0..k-1 ==> 0 < n i) /\
     (!i j:num.
        i IN 0..k-1 /\ j IN 0..k-1 /\ i < j
        ==> n i < n j) /\
     zpoly =
       (\z:complex.
          Cx(&1) +
          iterate ((+):complex->complex->complex)
            (0..k-1) (\i:num. z pow (n i)))
     ==> !z:complex.
           norm z < (sqrt(&5) - &1) / &2
           ==> ~(zpoly z = Cx(&0))`;;
