(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_b3
  (putnambench__hol-light__putnam_2017_b3): irrationality at one half of a
  real power series with coefficients in {0,1} whose value at two thirds is
  three halves. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let is_rational =
     \x:real.
       ?p q:int.
         ~(q = (&0:int)) /\
         x = real_of_int p / real_of_int q in
   !c:num->real.
     (!n:num. c n = &0 \/ c n = &1) /\
     suminf (\n:num. c n * (&2 / &3) pow n) = &3 / &2
     ==> ~is_rational
           (suminf (\n:num. c n * (&1 / &2) pow n))`;;
