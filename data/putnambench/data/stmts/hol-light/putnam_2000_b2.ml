(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_b2:
  the divisibility of the product of gcd(m,n) and the binomial coefficient
  n choose m by n whenever 1 <= m <= n. This file contains no proof.
*)

let binomial_output = open_out "/dev/null";;
let binomial_formatter = Format.formatter_of_out_channel binomial_output;;
let binomial_loaded =
  Toploop.use_file binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush binomial_formatter ();;
close_out binomial_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;

let statement =
  `!m n:num.
     1 <= m /\ m <= n
     ==> n divides (gcd(m,n) * binom (n,m))`;;
