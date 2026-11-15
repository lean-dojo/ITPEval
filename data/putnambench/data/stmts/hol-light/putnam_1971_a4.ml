(*
  Statement-only formalization of PutnamBench artifact putnam_1971_a4:
  multiplying a positive quadratic form by a sufficiently high power of
  x + y yields strictly positive coefficients throughout its homogeneous
  support.
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
  `!epsilon:real.
     &0 < epsilon /\ epsilon < &1
     ==>
     ?N:num.
       !n:num.
         N <= n
         ==>
         !i:num.
           i <= n + 2
           ==>
           &0 <
             (if 2 <= i then &(binom(n,i - 2)) else &0) -
             (&2 - epsilon) *
               (if 1 <= i then &(binom(n,i - 1)) else &0) +
             &(binom(n,i))`;;
