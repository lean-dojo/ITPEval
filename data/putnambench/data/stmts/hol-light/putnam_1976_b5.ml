(*
  Statement-only formalization of PutnamBench artifact putnam_1976_b5:
  the alternating binomial sum of the nth powers of x - k is the constant
  n factorial for every natural n and real x. This file contains no proof.
*)

let binomial_output = open_out "/dev/null";;
let binomial_formatter = Format.formatter_of_out_channel binomial_output;;
let binomial_loaded =
  Toploop.use_file binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush binomial_formatter ();;
close_out binomial_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;

let statement =
  `!n:num. !x:real.
     sum (0..n)
         (\k. (-- &1) pow k *
              &(binom (n,k)) *
              (x - &k) pow n) =
     &(FACT n)`;;
