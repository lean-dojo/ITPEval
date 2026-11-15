(*
  Statement-only formalization of PutnamBench artifact putnam_1974_a4:
  the closed form for a normalized lower-half binomial sum for every positive
  integer n. This file contains no proof.
*)

let binomial_output = open_out "/dev/null";;
let binomial_formatter = Format.formatter_of_out_channel binomial_output;;
let binomial_loaded =
  Toploop.use_file binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush binomial_formatter ();;
close_out binomial_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;

let statement =
  `!n:num.
     0 < n
     ==> (&1 / (&2 pow (n - 1))) *
         sum (0..n DIV 2)
             (\k. (&n - &2 * &k) * &(binom (n,k))) =
         (&n / (&2 pow (n - 1))) *
         &(binom (n - 1,n DIV 2))`;;
