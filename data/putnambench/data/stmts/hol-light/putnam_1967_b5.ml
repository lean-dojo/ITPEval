(*
  Statement-only formalization of PutnamBench artifact putnam_1967_b5:
  a finite initial sum of the negative binomial expansion at 2 equals one
  half for every positive integer parameter. This file contains no proof.
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
     ==> &1 / &2 =
         sum (0..n - 1)
             (\i. &(binom (n + i - 1,i)) / (&2 pow (n + i)))`;;
