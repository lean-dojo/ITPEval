(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_b5:
  a differentiable real function satisfying a specified nonlinear differential
  equation on (1,infinity) tends to positive infinity. This file contains no
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
     \(f:real->real) (x:real). @d:real. (f diffl d) x in
   let tends_to_posinfinity =
     \(f:real->real).
       !M:real.
         ?N:real.
           !x:real. N <= x ==> M <= f x in
   !f:real->real.
     (!x:real. &1 < x ==> f differentiable x) /\
     (!x:real.
        &1 < x
        ==> deriv f x =
            (x pow 2 - (f x) pow 2) /
            (x pow 2 * ((f x) pow 2 + &1)))
     ==>
     tends_to_posinfinity f`;;
