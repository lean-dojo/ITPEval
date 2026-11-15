(*
  Statement-only formalization of PutnamBench artifact putnam_1967_a4:
  nonexistence, for lambda greater than one half, of an integrable real
  function satisfying a nonlinear interval integral equation. This file
  contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!lam:real.
     lam > &1 / &2
     ==> ~(?u:real->real.
             integrable(&0,&1) u /\
             (!x:real.
                &0 <= x /\ x <= &1
                ==> integrable(x,&1) (\y. u y * u (y - x))) /\
             !x:real.
               &0 <= x /\ x <= &1
               ==> u x =
                   &1 + lam *
                   integral(x,&1) (\y. u y * u (y - x)))`;;
