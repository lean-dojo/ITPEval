(*
  Statement-only formalization of PutnamBench artifact putnam_1981_a3:
  nonexistence of a finite real limit at positive infinity for a scaled
  double integral involving the exponential difference quotient. This file
  contains no proof.
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
   let f =
     \t:real.
       exp (--t) *
       integral(&0,t)
         (\y:real.
            integral(&0,t)
              (\x:real. (exp x - exp y) / (x - y))) in
   ((?l:real. tends_at_posinfinity f l) <=> F)`;;
