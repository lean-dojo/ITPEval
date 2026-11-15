(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_b6:
  evaluation as pi^2/16 of the alternating series whose kth coefficient
  counts the odd divisors of k below sqrt(2k). This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `!A:num->num.
     (!k:num.
        0 < k
        ==>
        A k =
        CARD
          {j:num |
             ODD j /\
             j divides k /\
             &j < sqrt (&(2 * k))})
     ==>
     (\n:num.
        (--(&1)) pow n * &(A (n + 1)) / &(n + 1))
     sums (pi pow 2 / &16)`;;
