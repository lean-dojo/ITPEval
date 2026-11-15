(*
  Statement-only formalization of PutnamBench artifact putnam_1983_a4:
  the alternating sum of binomial coefficients in positions congruent to two
  modulo three is nonzero when the upper index is five modulo six. This file
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
  `!k m:num. !S:int.
     0 < k /\
     m = 6 * k - 1 /\
     S =
     isum (1..2 * k - 1)
          (\j. (-- &1) pow (j + 1) * &(binom (m,3 * j - 1)))
     ==> ~(S = &0)`;;
