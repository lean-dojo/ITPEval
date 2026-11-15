(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_a2
  (putnambench__hol-light__putnam_2020_a2): evaluation of a finite sum of
  powers of two times binomial coefficients. This file contains no proof.
*)

let binomial_output = open_out "/dev/null";;
let binomial_formatter = Format.formatter_of_out_channel binomial_output;;
let binomial_loaded =
  Toploop.use_file binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush binomial_formatter ();;
close_out binomial_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;

let statement =
  `!k:num.
     nsum (0..k) (\j. 2 EXP (k - j) * binom (k + j,j)) = 4 EXP k`;;
