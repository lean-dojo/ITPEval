(*
  Statement-only formalization of PutnamBench artifact putnam_1981_b1:
  evaluation as -1 of the limit of a normalized finite double sum of a
  quartic polynomial in its two indices. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `(\n:num.
      (&1 / ((&n) pow 5)) *
      sum (1..n)
        (\h:num.
           sum (1..n)
             (\k:num.
                &5 * (&h) pow 4 -
                &18 * (&h) pow 2 * (&k) pow 2 +
                &5 * (&k) pow 4)))
   tends_num_real (-- &1)`;;
