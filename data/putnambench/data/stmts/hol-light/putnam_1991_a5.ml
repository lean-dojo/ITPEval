(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_a5:
  the maximum over 0 <= y <= 1 of the integral from 0 to y of
  sqrt(x^4 + (y - y^2)^2) is 1/3. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let f =
     \y:real.
       integral(&0,y)
         (\x:real. sqrt (x pow 4 + (y - y pow 2) pow 2)) in
   (?y:real.
      &0 <= y /\
      y <= &1 /\
      f y = &1 / &3) /\
   (!y:real.
      &0 <= y /\ y <= &1
      ==> f y <= &1 / &3)`;;
