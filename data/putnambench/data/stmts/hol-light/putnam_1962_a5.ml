(*
  Statement-only formalization of PutnamBench artifact putnam_1962_a5:
  the closed form for the sum from k = 1 through n of the binomial
  coefficient n choose k times k squared. This file contains no proof.
*)

let binomial_output = open_out "/dev/null";;
let binomial_formatter = Format.formatter_of_out_channel binomial_output;;
let binomial_loaded =
  Toploop.use_file binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush binomial_formatter ();;
close_out binomial_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;

let statement =
  `let putnam_1962_a5_solution =
     \n:num. n * (n + 1) * 2 EXP (n - 2) in
   !n:num.
     2 <= n
     ==> putnam_1962_a5_solution n =
         nsum (1..n) (\k. binom (n,k) * k EXP 2)`;;
