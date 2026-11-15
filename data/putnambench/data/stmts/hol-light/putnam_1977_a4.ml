(*
  Statement-only formalization of PutnamBench artifact putnam_1977_a4:
  the dyadic-power series on the real interval (0,1) equals the rational
  function x / (1 - x). This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let putnam_1977_a4_solution =
     \x:real. x / (&1 - x) in
   !x:real.
     &0 < x /\ x < &1
     ==> putnam_1977_a4_solution x =
         suminf
           (\n:num.
              x pow (2 EXP n) /
              (&1 - x pow (2 EXP (n + 1))))`;;
