(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_b2
  (putnambench__hol-light__putnam_2021_b2): the maximum value 2/3 of a
  weighted infinite sum of geometric means over nonnegative real sequences
  summing to 1. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let total_sum =
     \f:num->real. if summable f then suminf f else &0 in
   let rpow =
     \x p:real. if x = &0 then &0 else exp (p * ln x) in
   let admissible =
     \a:num->real.
       (!k:num. &0 <= a k) /\ total_sum a = &1 in
   let score =
     \a:num->real.
       total_sum
         (\n:num.
            (&(n + 1) / (&2 pow (n + 1))) *
            rpow (product (0..n) a) (&1 / &(n + 1))) in
   (?a:num->real. admissible a /\ score a = &2 / &3) /\
   (!a:num->real. admissible a ==> score a <= &2 / &3)`;;
