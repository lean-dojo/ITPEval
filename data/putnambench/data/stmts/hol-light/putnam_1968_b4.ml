(*
  Statement-only formalization of PutnamBench artifact putnam_1968_b4:
  invariance of a convergent symmetric improper integral under the
  substitution x - 1/x. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let tends_at_posinfinity =
     \(g:real->real) (r:real).
       !e:real.
         &0 < e
         ==> ?B:real.
               !y:real. B <= y ==> abs (g y - r) < e in
   let symmetric_integral =
     \(f:real->real) (y:real).
       integral(--y,y) f in
   let punctured_symmetric_integral =
     \(f:real->real) (y:real).
       integral(--y,--(&1 / y)) f +
       integral(&1 / y,y) f in
   !f:real->real.
     (!x:real. f contl x) /\
     (?r:real. tends_at_posinfinity (symmetric_integral f) r)
     ==>
     ?r:real.
       tends_at_posinfinity
         (\y:real.
            punctured_symmetric_integral
              (\x:real. f (x - &1 / x)) y)
         r /\
       tends_at_posinfinity (symmetric_integral f) r`;;
