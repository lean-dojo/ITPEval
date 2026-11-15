(*
  Statement-only formalization of PutnamBench artifact putnam_1962_a4:
  bounds for a twice-differentiable real function on an interval imply a
  uniform bound on its first derivative. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let deriv =
     \(g:real->real) (x:real). @d. (g diffl d) x in
   !f:real->real. !a b:real.
     (!x. f differentiable x) /\
     (!x. deriv f differentiable x) /\
     (!x. a <= x /\ x <= b ==> abs(f x) <= &1) /\
     (!x. a <= x /\ x <= b ==> abs(deriv (deriv f) x) <= &1) /\
     b - a >= &2
     ==> !x. a <= x /\ x <= b ==> abs(deriv f x) <= &2`;;
