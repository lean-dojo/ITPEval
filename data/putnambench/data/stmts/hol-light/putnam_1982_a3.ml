(*
  Statement-only formalization of PutnamBench artifact putnam_1982_a3:
  evaluation of an improper integral involving the difference of two
  arctangent functions as (pi / 2) * ln pi. This file contains no proof.
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
     \(g:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?B:real.
               !t:real. B <= t ==> abs (g t - l) < e in
   let putnam_1982_a3_solution = (pi / &2) * ln pi in
   tends_at_posinfinity
     (\t:real.
        integral(&0,t)
          (\x:real. (atn (pi * x) - atn x) / x))
     putnam_1982_a3_solution`;;
