(*
  Statement-only formalization of PutnamBench artifact putnam_1965_a6:
  equivalence between the positive tangent-point equations for a real-power
  curve and a conjugate-exponent equation. This file contains no proof.
*)

let transc_output = open_out "/dev/null";;
let transc_formatter = Format.formatter_of_out_channel transc_output;;
let transc_loaded =
  Toploop.use_file transc_formatter "Library/transc.ml";;
Format.pp_print_flush transc_formatter ();;
close_out transc_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `!u v m:real.
     &0 < u /\ &0 < v /\ &1 < m
     ==>
     (((?x y:real.
          &0 < x /\
          &0 < y /\
          u * x + v * y = &1 /\
          exp (m * ln x) + exp (m * ln y) = &1 /\
          u = exp ((m - &1) * ln x) /\
          v = exp ((m - &1) * ln y)) <=>
       (?n:real.
          exp (n * ln u) + exp (n * ln v) = &1 /\
          &1 / m + &1 / n = &1)))`;;
