(*
  Statement-only formalization of PutnamBench artifact putnam_1969_b5:
  a strictly increasing positive integer sequence with convergent reciprocal
  series has a counting function that is sublinear at positive infinity.
  This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!a:num->num.
     !k:num->num.
       (!m n:num. m < n ==> a m < a n) /\
       (!n:num. 0 < a n) /\
       summable (\n:num. &1 / &(a n)) /\
       (!x:num. k x = CARD {n:num | a n <= x})
       ==> !e:real.
             &0 < e
             ==> ?N:num.
                   !t:num.
                     N <= t ==> abs (&(k t) / &t - &0) < e`;;
