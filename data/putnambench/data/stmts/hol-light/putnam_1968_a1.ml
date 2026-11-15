(*
  Statement-only formalization of PutnamBench artifact putnam_1968_a1:
  evaluation of a definite integral of a rational polynomial expression as
  22/7 minus pi. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `&22 / &7 - pi =
   integral(&0,&1)
     (\x. x pow 4 * (&1 - x) pow 4 / (&1 + x pow 2))`;;
