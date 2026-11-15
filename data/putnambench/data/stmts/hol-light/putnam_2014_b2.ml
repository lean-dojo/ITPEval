(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_b2:
  the greatest possible integral of f(x)/x on [1,3] among integrable functions
  bounded between -1 and 1 with zero integral is ln(4/3). This file contains
  no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let admissible =
     \(f:real->real).
       (!x:real.
          &1 <= x /\ x <= &3
          ==> -- &1 <= f x /\ f x <= &1) /\
       integrable(&1,&3) f /\
       integral(&1,&3) f = &0 in
   let objective =
     \(f:real->real). integral(&1,&3) (\x:real. f x / x) in
   (?f:real->real.
      admissible f /\ objective f = ln (&4 / &3)) /\
   (!f:real->real.
      admissible f ==> objective f <= ln (&4 / &3))`;;
