(*
  Statement-only formalization of PutnamBench artifact putnam_1967_b6:
  a real function with both partial derivatives everywhere and
  bounded on the closed disk has an interior point where the sum of the
  squares of its partial derivatives is at most 16. This file contains no
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
     \(g:real->real) (x:real). @d. (g diffl d) x in
   !f:real->real->real.
     (!x y:real.
        (\t. f t y) differentiable x /\
        (\t. f x t) differentiable y) /\
     (!x y:real.
        x pow 2 + y pow 2 <= &1 ==> abs (f x y) <= &1)
     ==> ?x0 y0:real.
           x0 pow 2 + y0 pow 2 < &1 /\
           (deriv (\x. f x y0) x0) pow 2 +
           (deriv (\y. f x0 y) y0) pow 2 <= &16`;;
