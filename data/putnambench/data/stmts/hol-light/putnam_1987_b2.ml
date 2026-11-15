(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_b2:
  the finite sum identity for ratios of binomial coefficients under the
  constraint r + s <= t. This file contains no proof.
*)

let binomial_output = open_out "/dev/null";;
let binomial_formatter = Format.formatter_of_out_channel binomial_output;;
let binomial_loaded =
  Toploop.use_file binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush binomial_formatter ();;
close_out binomial_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;

let statement =
  `!r s t:num.
     r + s <= t
     ==> sum (0..s)
             (\i. &(binom (s,i)) / &(binom (t,r + i))) =
         &(t + 1) / (&(t + 1 - s) * &(binom (t - s,r)))`;;
