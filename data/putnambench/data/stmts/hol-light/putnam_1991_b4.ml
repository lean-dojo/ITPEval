(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_b4:
  a binomial-sum congruence modulo the square of an odd prime. This file
  contains no proof.
*)

let binomial_output = open_out "/dev/null";;
let binomial_formatter = Format.formatter_of_out_channel binomial_output;;
let binomial_loaded =
  Toploop.use_file binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush binomial_formatter ();;
close_out binomial_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;

let statement =
  `!p:num.
     ODD p /\ prime p
     ==>
     nsum (0..p) (\j. binom (p,j) * binom (p + j,j)) MOD (p EXP 2) =
     (2 EXP p + 1) MOD (p EXP 2)`;;
