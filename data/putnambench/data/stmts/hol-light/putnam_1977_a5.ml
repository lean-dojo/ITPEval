(*
  Statement-only formalization of PutnamBench artifact putnam_1977_a5:
  the binomial coefficient congruence modulo a prime for scaled indices.
  This file contains no proof.
*)

let binomial_output = open_out "/dev/null";;
let binomial_formatter = Format.formatter_of_out_channel binomial_output;;
let binomial_loaded =
  Toploop.use_file binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush binomial_formatter ();;
close_out binomial_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;

let statement =
  `!p m n:num.
     prime p /\ m >= n
     ==> binom (p * m,p * n) MOD p = binom (m,n) MOD p`;;
