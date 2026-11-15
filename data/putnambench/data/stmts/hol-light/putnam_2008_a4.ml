(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_a4:
  the recursively defined real function using logarithmic descent has a
  divergent reciprocal series. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let putnam_2008_a4_solution = F in
   !f:real->real.
     (!x:real.
        f x =
        if x <= exp (&1) then x else x * f (ln x))
     ==>
     (summable (\n:num. &1 / f (&(n + 1))) <=>
      putnam_2008_a4_solution)`;;
