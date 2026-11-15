(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_b3:
  classification of positive differentiable functions on the positive reals
  satisfying a derivative functional equation. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let deriv =
     \(g:real->real) (x:real). @d:real. (g diffl d) x in
   let rpow =
     \x p:real. exp (p * ln x) in
   !f:real->real.
     (!x:real. &0 < x ==> &0 < f x) /\
     (!x:real. &0 < x ==> f differentiable x)
     ==>
     ((?a:real.
         &0 < a /\
         !x:real.
           &0 < x ==> deriv f (a / x) = x / f x)
      <=>
      (?c d:real.
         &0 < c /\
         &0 < d /\
         (d = &1 ==> c = &1) /\
         !x:real.
           &0 < x ==> f x = c * rpow x d))`;;
