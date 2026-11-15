(*
  Statement-only formalization of PutnamBench artifact putnam_1965_a3:
  equivalence of convergence for complex exponential averages over the first
  n terms and over the first n squared terms. This file contains no proof.
*)

let complex_output = open_out "/dev/null";;
let complex_formatter = Format.formatter_of_out_channel complex_output;;
let complex_loaded =
  Toploop.use_file complex_formatter "Complex/complexnumbers.ml";;
Format.pp_print_flush complex_formatter ();;
close_out complex_output;;
if not complex_loaded then
  failwith "failed to load Complex/complexnumbers.ml";;

let statement =
  `!a:num->real. !alpha:complex.
     (((\n:num. sum (1..n) (\k. cos(a k)) / &n)
         tends_num_real Re(alpha)) /\
       ((\n:num. sum (1..n) (\k. sin(a k)) / &n)
         tends_num_real Im(alpha)) <=>
      ((\n:num. sum (1..(n EXP 2)) (\k. cos(a k)) / &(n EXP 2))
         tends_num_real Re(alpha)) /\
       ((\n:num. sum (1..(n EXP 2)) (\k. sin(a k)) / &(n EXP 2))
         tends_num_real Im(alpha)))`;;
