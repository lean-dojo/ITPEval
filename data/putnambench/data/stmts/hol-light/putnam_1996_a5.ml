(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_a5:
  divisibility by the square of a prime of an initial sum of its binomial
  coefficients, with endpoint floor(2p/3). This file contains no proof.
*)

let binomial_output = open_out "/dev/null";;
let binomial_formatter = Format.formatter_of_out_channel binomial_output;;
let binomial_loaded =
  Toploop.use_file binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush binomial_formatter ();;
close_out binomial_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;

let statement =
  `!p k:num.
     prime p /\ p > 3 /\ k = (2 * p) DIV 3
     ==>
     p EXP 2 divides nsum (1..k) (\i. binom (p,i))`;;
