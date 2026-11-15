(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_b1:
  classification of continuously differentiable real functions satisfying an
  integral identity involving the squares of the function and its derivative.
  This file contains no proof.
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
     \(f:real->real) (x:real). @d:real. (f diffl d) x in
   let continuous =
     \(f:real->real).
       !x e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 abs (y - x) < delta ==> abs (f y - f x) < e in
   let continuously_differentiable =
     \(f:real->real).
       (!x:real. (f diffl (deriv f x)) x) /\
       continuous (deriv f) in
   let interval_integral =
     \(f:real->real) (x:real).
       if &0 <= x
       then integral(&0,x) f
       else --(integral(x,&0) f) in
   !f:real->real.
     (continuously_differentiable f /\
      (!x:real.
         (f x) pow 2 =
         interval_integral
           (\t:real. (f t) pow 2 + (deriv f t) pow 2)
           x +
         &1990))
     <=>
     (f = (\x:real. sqrt (&1990) * exp x) \/
      f = (\x:real. --(sqrt (&1990) * exp x)))`;;
