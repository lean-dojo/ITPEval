(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_b2:
  two nonconstant differentiable real functions satisfying the complex
  addition laws have values on the unit circle when the first function has
  derivative zero at the origin. This file contains no proof.
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
     \(h:real->real) (x:real). @d:real. (h diffl d) x in
   !f g:real->real.
     ~(?c:real. f = (\x:real. c) \/ g = (\x:real. c)) /\
     (!x:real. f differentiable x) /\
     (!x:real. g differentiable x) /\
     (!x y:real.
        f (x + y) = f x * f y - g x * g y) /\
     (!x y:real.
        g (x + y) = f x * g y + g x * f y)
     ==>
     (deriv f (&0) = &0
      ==> !x:real. (f x) pow 2 + (g x) pow 2 = &1)`;;
