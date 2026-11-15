(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_b5:
  continuously differentiable real functions preserving the reduced
  denominator of every rational input are exactly integer translates of the
  identity or its negation. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let rat_value =
     \q:int#num. real_of_int (FST q) / &(SND q) in
   let reduced =
     \q:int#num.
       0 < SND q /\ coprime (num_of_int (abs (FST q)),SND q) in
   let continuous =
     \(g:real->real).
       !x e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 abs (y - x) < delta ==> abs (g y - g x) < e in
   let continuously_differentiable =
     \(f:real->real).
       ?f':real->real.
         (!x:real. (f diffl (f' x)) x) /\
         continuous f' in
   let preserves_reduced_denominator =
     \(f:real->real).
       !q:int#num.
         reduced q
         ==> ?p:int#num.
               reduced p /\
               SND p = SND q /\
               f (rat_value q) = rat_value p in
   let solution =
     \(f:real->real).
       ?n:int.
         f = (\x:real. x + real_of_int n) \/
         f = (\x:real. --x + real_of_int n) in
   !f:real->real.
     (continuously_differentiable f /\
      preserves_reduced_denominator f
      <=> solution f)`;;
