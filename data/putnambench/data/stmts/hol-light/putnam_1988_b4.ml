(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_b4:
  positive real series remain positive and convergent after raising the nth
  term to the real exponent n/(n+1). This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let rpow =
     \x p:real. exp (p * ln x) in
   let is_positive =
     \a:num->real. !n:num. 1 <= n ==> &0 < a n in
   let has_convergent_partial_sums =
     \a:num->real.
       ?L:real. (\N:num. sum (1..N) a) tends_num_real L in
   !a:num->real.
     is_positive a /\ has_convergent_partial_sums a
     ==>
     is_positive
       (\n:num. rpow (a n) (&n / (&n + &1))) /\
     has_convergent_partial_sums
       (\n:num. rpow (a n) (&n / (&n + &1)))`;;
