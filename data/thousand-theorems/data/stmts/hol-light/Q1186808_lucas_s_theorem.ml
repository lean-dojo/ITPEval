(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1186808,
  "Lucas's theorem": for a prime p, a binomial coefficient is congruent
  modulo p to the product of the binomial coefficients of the corresponding
  base-p digits. This file contains no proof.
*)

let lucas_binomial_output = open_out "/dev/null";;
let lucas_binomial_formatter =
  Format.formatter_of_out_channel lucas_binomial_output;;
let lucas_binomial_loaded =
  Toploop.use_file lucas_binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush lucas_binomial_formatter ();;
close_out lucas_binomial_output;;
if not lucas_binomial_loaded then
  failwith "failed to load Library/binomial.ml";;

let Q1186808_LUCAS_THEOREM =
  `!p n k a:num.
     prime p /\
     n < p EXP a /\
     k < p EXP a
     ==> (binom (n,k) ==
          nproduct {i | i < a}
            (\i. binom ((n DIV (p EXP i)) MOD p,
                        (k DIV (p EXP i)) MOD p))) (mod p)`;;
