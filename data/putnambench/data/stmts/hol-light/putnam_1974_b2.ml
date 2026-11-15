(*
  Statement-only formalization of PutnamBench artifact putnam_1974_b2:
  a continuously differentiable real function whose squared derivative plus
  cubed value tends to zero at positive infinity has both the function and
  its derivative tend to zero there. This file contains no proof.
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
     \(f:real->real) (x:real). @d. (f diffl d) x in
   let continuous =
     \(f:real->real).
       !x e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !z:real. abs (z - x) < d ==> abs (f z - f x) < e in
   let continuously_differentiable =
     \(f:real->real).
       (!x:real. (f diffl (deriv f x)) x) /\
       continuous (deriv f) in
   let tends_at_posinfinity =
     \(f:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?B:real.
               !x:real. B <= x ==> abs (f x - l) < e in
   !y:real->real.
     continuously_differentiable y /\
     tends_at_posinfinity
       (\x:real. (deriv y x) pow 2 + (y x) pow 3)
       (&0)
     ==>
     tends_at_posinfinity y (&0) /\
     tends_at_posinfinity (deriv y) (&0)`;;
