(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_b1:
  a three-times differentiable real function with at least five distinct
  zeros makes f + 6f' + 12f'' + 8f''' have at least two distinct real zeros.
  This file contains no proof.
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
   let g =
     \(h:real->real) (x:real).
       h x +
       &6 * deriv h x +
       &12 * deriv (deriv h) x +
       &8 * deriv (deriv (deriv h)) x in
   !f:real->real.
     (!x:real. f differentiable x) /\
     (!x:real. deriv f differentiable x) /\
     (!x:real. deriv (deriv f) differentiable x) /\
     (?x1 x2 x3 x4 x5:real.
        ~(x1 = x2) /\
        ~(x1 = x3) /\
        ~(x1 = x4) /\
        ~(x1 = x5) /\
        ~(x2 = x3) /\
        ~(x2 = x4) /\
        ~(x2 = x5) /\
        ~(x3 = x4) /\
        ~(x3 = x5) /\
        ~(x4 = x5) /\
        f x1 = &0 /\
        f x2 = &0 /\
        f x3 = &0 /\
        f x4 = &0 /\
        f x5 = &0)
     ==>
     ?y1 y2:real.
       ~(y1 = y2) /\
       g f y1 = &0 /\
       g f y2 = &0`;;
