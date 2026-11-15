(*
  Statement-only formalization of PutnamBench artifact putnam_1965_a2:
  the finite binomial-square sum identity for every positive integer n.
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
  `!n:num.
     0 < n
     ==> sum (0..(n - 1) DIV 2)
             (\r. (&(n - 2 * r) * &(binom (n,r)) / &n) pow 2) =
         &(binom (2 * n - 2,n - 1)) / &n`;;
