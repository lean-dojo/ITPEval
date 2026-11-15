(*
  Statement-only formalization of PutnamBench artifact putnam_1976_a6:
  existence of a real zero of f + f'' for a globally bounded twice
  continuously differentiable real function satisfying the prescribed
  initial-value equation. This file contains no proof.
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
   let continuous =
     \(g:real->real).
       !x e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !z:real.
                 abs (z - x) < delta ==> abs (g z - g x) < e in
   let twice_continuously_differentiable =
     \(g:real->real).
       (!x:real. g differentiable x) /\
       (!x:real. (deriv g) differentiable x) /\
       continuous (deriv g) /\
       continuous (deriv (deriv g)) in
   !f:real->real.
     twice_continuously_differentiable f /\
     (!x:real. abs (f x) <= &1) /\
     (f (&0)) pow 2 + (deriv f (&0)) pow 2 = &4
     ==> ?y:real. f y + deriv (deriv f) y = &0`;;
