(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_a6:
  the positive real parameters for which the series weighted by the number
  of zeroes in each index's base-3 representation converges. This file
  contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let zero_count =
     \n:num.
       CARD
         {i:num |
            3 EXP i <= n /\
            (n DIV (3 EXP i)) MOD 3 = 0} in
   {x:real |
      &0 < x /\
      summable
        (\n:num.
           x pow (zero_count n) / &(n EXP 3))} =
   {x:real | &0 < x /\ x < &25}`;;
