(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_b4:
  the composition of equal-angle counterclockwise rotations about the points
  1 through n in the complex plane is translation by n. This file contains
  no proof.
*)

let complex_transc_output = open_out "/dev/null";;
let complex_transc_formatter =
  Format.formatter_of_out_channel complex_transc_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file complex_transc_formatter path);;
let complex_transc_loaded =
  Toploop.use_file complex_transc_formatter "Complex/complex_transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush complex_transc_formatter ();;
close_out complex_transc_output;;
if not complex_transc_loaded then
  failwith "failed to load Complex/complex_transc.ml";;

let statement =
  `!n:num. !R Rk:num->complex->complex.
     2 <= n /\
     Rk =
       (\k Q.
          Cx(&k) +
          cexp (ii * Cx(&2 * pi / &n)) * (Q - Cx(&k))) /\
     R 0 = (\z:complex. z) /\
     (!k:num. R (k + 1) = Rk (k + 1) o R k)
     ==>
     R n = (\z:complex. z + Cx(&n))`;;
