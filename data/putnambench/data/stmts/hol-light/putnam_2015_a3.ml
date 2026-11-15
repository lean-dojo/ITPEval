(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_a3:
  the base-2 principal complex logarithm of a double product of complex
  exponentials over the integers from 1 through 2015 equals 13725. This file
  contains no proof.
*)

let complex_transc_output = open_out "/dev/null";;
let complex_transc_formatter =
  Format.formatter_of_out_channel complex_transc_output;;
let previous_std_formatter_out_functions =
  Format.pp_get_formatter_out_functions Format.std_formatter ();;
let previous_file_loader = !Hol_loader.file_loader;;
Format.pp_set_formatter_out_channel
  Format.std_formatter complex_transc_output;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file complex_transc_formatter path);;
let complex_transc_loaded =
  Toploop.use_file complex_transc_formatter "Complex/complex_transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_set_formatter_out_functions
  Format.std_formatter previous_std_formatter_out_functions;;
Format.pp_print_flush complex_transc_formatter ();;
close_out complex_transc_output;;
if not complex_transc_loaded then
  failwith "failed to load Complex/complex_transc.ml";;

let statement =
  `let cproduct =
     \s f. iterate (( * ):complex->complex->complex) s f in
   clog
     (cproduct (1..2015)
        (\a. cproduct (1..2015)
          (\b. Cx(&1) +
               cexp(Cx(&2 * pi * &a * &b / &2015) * ii))))
   / clog(Cx(&2)) =
   Cx(&13725)`;;
