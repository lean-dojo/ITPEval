(*
  Statement-only formalization of PutnamBench artifact putnam_1972_b1:
  no three consecutive coefficients in the power-series expansion near zero
  of a specified factorial series all vanish. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let total_sum =
     \f:num->real. if summable f then suminf f else &0 in
   !S:real->real. !p:num->real.
     S =
       (\x. total_sum
              (\n:num.
                 x pow n * (x - &1) pow (2 * n) / &(FACT n))) /\
     (?a:real.
        &0 < a /\
        !x:real.
          abs x < a
          ==> total_sum (\n:num. p n * x pow n) = S x)
     ==> ~(?n:num.
              p n = &0 /\
              p (n + 1) = &0 /\
              p (n + 2) = &0)`;;
