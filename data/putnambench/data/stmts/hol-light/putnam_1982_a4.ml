(*
  Statement-only formalization of PutnamBench artifact putnam_1982_a4:
  periodicity of the unique global continuously differentiable solution of
  y' = -z^3 and z' = y^3 with initial value (1,0). This file contains no proof.
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
     \(h:real->real) (x:real). @d. (h diffl d) x in
   let continuous =
     \(h:real->real).
       !x e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !u:real.
                 abs (u - x) < delta ==> abs (h u - h x) < e in
   let continuously_differentiable =
     \(h:real->real).
       (!x:real. (h diffl (deriv h x)) x) /\
       continuous (deriv h) in
   let hdiffeq =
     \(y:real->real) (z:real->real).
       y (&0) = &1 /\
       z (&0) = &0 /\
       continuously_differentiable y /\
       continuously_differentiable z /\
       (!x:real.
          deriv y x = --((z x) pow 3) /\
          deriv z x = (y x) pow 3) in
   !f g:real->real.
     hdiffeq f g /\
     ~(?f' g':real->real.
         (~(f = f') \/ ~(g = g')) /\ hdiffeq f' g')
     ==> ?L:real.
           &0 < L /\
           !x:real.
             f (x + L) = f x /\
             g (x + L) = g x`;;
