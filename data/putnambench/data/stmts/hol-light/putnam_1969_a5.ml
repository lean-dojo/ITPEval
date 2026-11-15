(*
  Statement-only formalization of PutnamBench artifact putnam_1969_a5:
  controllability to the origin for a symmetric system of two real
  differential equations with a continuous control. This file contains no
  proof.
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
     \(g:real->real) (p:real). @d. (g diffl d) p in
   !x0 y0 t:real.
     &0 < t
     ==>
     (x0 = y0 <=>
      ?x y u:real->real.
        (!p. x differentiable p) /\
        (!p. y differentiable p) /\
        (!p. u contl p) /\
        (!p. deriv x p = --(&2) * y p + u p) /\
        (!p. deriv y p = --(&2) * x p + u p) /\
        x (&0) = x0 /\
        y (&0) = y0 /\
        x t = &0 /\
        y t = &0)`;;
