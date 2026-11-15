(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_a2:
  classification of differentiable real functions whose derivative equals
  every positive-integer forward difference quotient. This file contains no
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
   !f:real->real.
     (((!x:real. f differentiable x) /\
       (!x:real. !n:num.
          0 < n
          ==> deriv f x = (f (x + &n) - f x) / &n))
      <=>
      (?c d:real. !x:real. f x = c * x + d))`;;
