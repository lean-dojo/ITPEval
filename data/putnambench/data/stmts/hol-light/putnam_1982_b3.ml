(*
  Statement-only formalization of PutnamBench artifact putnam_1982_b3:
  the limiting probability, scaled by sqrt n, that the sum of two independent
  uniform choices from {1,...,n} is a perfect square. This file contains no
  proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!p:num->real.
     (!n:num.
        p n =
        &(CARD
            {(c,d):num#num |
               1 <= c /\ c <= n /\
               1 <= d /\ d <= n /\
               (?m:num. m EXP 2 = c + d)}) /
        (&n pow 2))
     ==> (\n:num. p n * sqrt (&n)) tends_num_real
         ((&4 / &3) * (sqrt (&2) - &1))`;;
