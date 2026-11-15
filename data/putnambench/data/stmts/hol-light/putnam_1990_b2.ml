(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_b2:
  the real infinite-series identity for coefficients defined by quotients of
  finite products when |x| < 1 and |z| > 1. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!x z:real. !P:num->real.
     abs x < &1 /\
     abs z > &1 /\
     (!j:num.
        1 <= j
        ==> P j =
            product (0..j-1) (\i:num. &1 - z * x pow i) /
            product (1..j) (\i:num. z - x pow i))
     ==> &1 +
         suminf
           (\j:num. (&1 + x pow (j + 1)) * P (j + 1)) =
         &0`;;
