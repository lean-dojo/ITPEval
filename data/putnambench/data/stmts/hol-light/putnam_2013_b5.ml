(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_b5:
  the number of endofunctions on {1,...,n} whose every orbit eventually
  reaches {1,...,k}. This file contains no proof.
*)

let iter_output = open_out "/dev/null";;
let iter_formatter = Format.formatter_of_out_channel iter_output;;
let iter_loaded =
  Toploop.use_file iter_formatter "Library/iter.ml";;
Format.pp_print_flush iter_formatter ();;
close_out iter_output;;
if not iter_loaded then failwith "failed to load Library/iter.ml";;

let statement =
  `!n k:num.
     1 <= n /\ k IN (1..n)
     ==>
     CARD
       {f:num->num |
          (!x:num. x IN (1..n) ==> f x IN (1..n)) /\
          (!x:num. ~(x IN (1..n)) ==> f x = 0) /\
          (!x:num.
             x IN (1..n)
             ==> ?j:num. ITER j f x <= k)} =
     k * n EXP (n - 1)`;;
