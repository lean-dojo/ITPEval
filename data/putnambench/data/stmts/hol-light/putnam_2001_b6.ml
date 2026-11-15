(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_b6:
  every positive strictly increasing sublinear real sequence has infinitely
  many terms strictly above the averages of all symmetric pairs around them.
  This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `((!a:num->real.
       (!n:num.
          1 <= n
          ==> &0 < a n /\ a n < a (n + 1)) /\
       ((\n:num. a (n + 1) / &(n + 1)) tends_num_real &0)
       ==>
       INFINITE
         {n:num |
            0 < n /\
            !i:num.
              1 <= i /\ i <= n - 1
              ==> a (n - i) + a (n + i) < &2 * a n})
    <=> T)`;;
