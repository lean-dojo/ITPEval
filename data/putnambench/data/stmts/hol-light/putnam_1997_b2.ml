(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_b2:
  boundedness of the absolute value of a twice-differentiable real function
  satisfying f(x) + f''(x) = -x g(x) f'(x) with nonnegative g.
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
   !f g:real->real.
     (!x:real. &0 <= g x) /\
     (!x:real. f differentiable x) /\
     (!x:real. deriv f differentiable x) /\
     (!x:real.
        f x + deriv (deriv f) x =
        --x * g x * deriv f x)
     ==> ?M:real.
           &0 <= M /\ !x:real. abs (f x) <= M`;;
