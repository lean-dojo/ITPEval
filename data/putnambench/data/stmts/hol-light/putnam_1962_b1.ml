(*
  Statement-only formalization of PutnamBench artifact putnam_1962_b1:
  the binomial convolution identity for real falling factorials.
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
  `!p:num->real->real. !x y:real. !n:num.
     p 0 = (\z. &1) /\
     (!m. 0 < m
          ==> p m =
              (\z. product (0..m-1) (\i. z - &i)))
     ==> p n (x + y) =
         sum (0..n)
             (\k. &(binom (n,k)) * p k x * p (n - k) y)`;;
