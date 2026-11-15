(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_a4:
  the smallest possible probability of zero for a nonnegative integer-valued
  random variable with first three moments 1, 2, and 5. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let admissible =
     \p:num->real.
       (!n:num. &0 <= p n /\ p n <= &1) /\
       summable p /\
       suminf p = &1 /\
       summable (\n:num. &n * p n) /\
       suminf (\n:num. &n * p n) = &1 /\
       summable (\n:num. (&n) pow 2 * p n) /\
       suminf (\n:num. (&n) pow 2 * p n) = &2 /\
       summable (\n:num. (&n) pow 3 * p n) /\
       suminf (\n:num. (&n) pow 3 * p n) = &5 in
   (!p:num->real. admissible p ==> &1 / &3 <= p 0) /\
   (?p:num->real. admissible p /\ p 0 = &1 / &3)`;;
