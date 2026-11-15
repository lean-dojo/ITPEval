(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_b6:
  the normalized power of a positive real sequence defined by a reciprocal
  k-th-root recurrence converges to ((k + 1) / k)^k. This file contains no
  proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let rpow =
     \x p:real. if x = &0 then &0 else exp (p * ln x) in
   !k:num. !a:num->real.
     1 < k /\
     &0 < a 0 /\
     (!n:num.
        a (n + 1) =
        a n + &1 / rpow (a n) (&1 / &k))
     ==>
     (\n:num. (a n) pow (k + 1) / (&n) pow k)
     tends_num_real
     ((&(k + 1) / &k) pow k)`;;
