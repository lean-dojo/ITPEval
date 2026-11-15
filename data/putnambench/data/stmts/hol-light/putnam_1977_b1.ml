(*
  Statement-only formalization of PutnamBench artifact putnam_1977_b1:
  the infinite product of (n^3 - 1) / (n^3 + 1) from n = 2 converges
  to 2/3. This file contains no proof.
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
      product (2..n)
        (\k:num.
           (((&k:real) pow 3) - &1) /
           (((&k:real) pow 3) + &1)))
   tends_num_real
   (&2 / &3)`;;
