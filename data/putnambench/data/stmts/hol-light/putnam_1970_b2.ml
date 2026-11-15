(*
  Statement-only formalization of PutnamBench artifact putnam_1970_b2:
  the average value of a real polynomial of degree at most three on a
  symmetric interval equals its symmetric two-point average at the Gaussian
  quadrature nodes. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let polynomial_degree_at_most_3 =
     \H:real->real.
       ?a0 a1 a2 a3:real.
         !x:real.
           H x =
           a0 + a1 * x + a2 * x pow 2 + a3 * x pow 3 in
   !t:real. !H:real->real.
     &0 < t /\ polynomial_degree_at_most_3 H
     ==>
     (H (--t / sqrt (&3)) + H (t / sqrt (&3))) / &2 =
     (&1 / (&2 * t)) * integral(--t,t) H`;;
